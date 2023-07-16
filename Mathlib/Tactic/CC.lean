/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.smt.congruence_closure
! leanprover-community/lean commit 9eae65f7144bcc692858b9dadf2e48181f4270b9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.CCLemmas
import Mathlib.Tactic.RunCmd
import Mathlib.Data.Vector
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Defs

/-!
## Congruence closures
-/

universe u

syntax (name := Lean.Parser.Tactic.cc) "cc" : tactic

namespace Mathlib.Tactic.CC

open Lean Meta Elab Tactic Parser.Tactic Std

initialize registerTraceClass `Meta.Tactic.cc

/-- Ordering on `Expr`. -/
def Expr.quickCmp (a b : Expr) : Ordering :=
  if Expr.quickLt a b then .lt else if a.eqv b then .eq else .gt

abbrev RBExprMap (α : Type u) := Std.RBMap Expr α Expr.quickCmp

abbrev UInt64Map (α : Type u) := Std.RBMap UInt64 α compare

structure CCConfig where
  /-- If `true`, congruence closure will treat implicit instance arguments as constants. -/
  ignoreInstances : Bool := true
  /-- If `true`, congruence closure modulo AC. -/
  ac : Bool := true
  /-- If `hoFns` is `some fns`, then full (and more expensive) support for higher-order functions is
     *only* considered for the functions in fns and local functions. The performance overhead is
     described in the paper "Congruence Closure in Intensional Type Theory". If `hoFns` is `none`,
     then full support is provided for *all* constants. -/
  hoFns : Option (List Name) := none
  /-- If `true`, then use excluded middle -/
  em : Bool := true
  /-- If `true`, we treat values as atomic symbols -/
  values := true
#align cc_config Mathlib.Tactic.CC.CCConfig

/-
TODO: Port these C++ code.
src/library/tactic/smt/congruence_closure.h:
```c++
namespace lean {
struct ext_congr_lemma;

struct ext_congr_lemma_cache;
typedef std::shared_ptr<ext_congr_lemma_cache> ext_congr_lemma_cache_ptr;

class cc_propagation_handler {
public:
    virtual ~cc_propagation_handler() {}
    virtual void propagated(unsigned n, expr const * data) = 0;
    void propagated(buffer<expr> const & p) { propagated(p.size(), p.data()); }
    /* Congruence closure module invokes the following method when
       a new auxiliary term is created during propagation. */
    virtual void new_aux_cc_term(expr const & e) = 0;
};

/* The congruence_closure module (optionally) uses a normalizer.
   The idea is to use it (if available) to normalize auxiliary expressions
   produced by internal propagation rules (e.g., subsingleton propagator). */
class cc_normalizer {
public:
    virtual ~cc_normalizer() {}
    virtual expr normalize(expr const & e) = 0;
};

class congruence_closure {
    /* Equivalence class data associated with an expression 'e' */
    struct entry {
        expr           m_next;       // next element in the equivalence class.
        expr           m_root;       // root (aka canonical) representative of the equivalence class.
        expr           m_cg_root;    // root of the congruence class, it is meaningless if 'e' is not an application.
        /* When 'e' was added to this equivalence class because of an equality (H : e = target), then we
           store 'target' at 'm_target', and 'H' at 'm_proof'. Both fields are none if 'e' == m_root */
        optional<expr> m_target;
        optional<expr> m_proof;
        /* Variable in the AC theory. */
        optional<expr> m_ac_var;
        unsigned       m_flipped:1;      // proof has been flipped
        unsigned       m_interpreted:1;  // true if the node should be viewed as an abstract value
        unsigned       m_constructor:1;  // true if head symbol is a constructor
        unsigned       m_has_lambdas:1;  // true if equivalence class contains lambda expressions
        /* m_heq_proofs == true iff some proofs in the equivalence class are based on heterogeneous equality.
           We represent equality and heterogeneous equality in a single equivalence class. */
        unsigned       m_heq_proofs:1;
        /* If m_fo == true, then the expression associated with this entry is an application, and
           we are using first-order approximation to encode it. That is, we ignore its partial applications. */
        unsigned       m_fo:1;
        unsigned       m_size;           // number of elements in the equivalence class, it is meaningless if 'e' != m_root
        /* The field m_mt is used to implement the mod-time optimization introduce by the Simplify theorem prover.
           The basic idea is to introduce a counter gmt that records the number of heuristic instantiation that have
           occurred in the current branch. It is incremented after each round of heuristic instantiation.
           The field m_mt records the last time any proper descendant of of thie entry was involved in a merge. */
        unsigned       m_mt;
        unsigned       m_generation;
    };

    struct parent_occ {
        expr m_expr;
        /* If m_symm_table is true, then we should use the m_symm_congruences, otherwise m_congruences.
           Remark: this information is redundant, it can be inferred from m_expr. We use store it for
           performance reasons. */
        bool m_symm_table;
        parent_occ() {}
        parent_occ(expr const & e, bool symm_table):m_expr(e), m_symm_table(symm_table) {}
    };

    struct parent_occ_cmp {
        int operator()(parent_occ const & k1, parent_occ const & k2) const {
            return expr_quick_cmp()(k1.m_expr, k2.m_expr);
        }
    };

    typedef rb_expr_map<entry>                           entries;
    typedef rb_tree<parent_occ, parent_occ_cmp>          parent_occ_set;
    typedef rb_expr_map<parent_occ_set>                  parents;
    typedef unsigned_map<list<expr>>                     congruences;
    typedef unsigned_map<list<pair<expr, name>>>         symm_congruences;
    typedef rb_expr_map<expr>                            subsingleton_reprs;
    typedef std::tuple<expr, expr, expr, bool>           todo_entry;

public:
    struct config {
        unsigned m_ignore_instances:1;
        unsigned m_values:1;
        unsigned m_all_ho:1;
        unsigned m_ac:1;
        unsigned m_em:1;
        config() { m_ignore_instances = true; m_values = true; m_all_ho = false; m_ac = true; m_em = true; }
    };

    class state {
        entries            m_entries;
        parents            m_parents;
        congruences        m_congruences;
        symm_congruences   m_symm_congruences;
        /** The following mapping store a representative for each subsingleton type */
        subsingleton_reprs m_subsingleton_reprs;
        /** The congruence closure module has a mode where the root of
            each equivalence class is marked as an interpreted/abstract
            value. Moreover, in this mode proof production is disabled.
            This capability is useful for heuristic instantiation. */
        short              m_froze_partitions{false};
        short              m_inconsistent{false};
        unsigned           m_gmt{0};
        /** Only for constant functions in m_ho_fns, we add the extra occurrences discussed in
            the paper "Congruence Closure in Intensional Type Theory". The idea is to avoid
            the quadratic number of entries in the parent occurrences data-structures,
            and avoid the creation of entries for partial applications. For example, given
            (@add nat nat_has_add a b), it seems wasteful to create entries for
            (@add nat), (@add nat nat_has_add) and (@nat nat_has_add a).
            This set is ignore if m_config.m_all_ho is true. */
        name_set           m_ho_fns;
        /* We are planning to have very few theories in this module. So, we don't
           use any abstract theory state object. */
        theory_ac::state   m_ac_state;
        config             m_config;
        friend class congruence_closure;
        bool check_eqc(expr const & e) const;
        void mk_entry_core(expr const & e, bool interpreted, bool constructor, unsigned gen);
    public:
        state(name_set const & ho_fns = name_set(), config const & cfg = config());
        void get_roots(buffer<expr> & roots, bool nonsingleton_only = true) const;
        expr get_root(expr const & e) const;
        expr get_next(expr const & e) const;
        unsigned get_mt(expr const & e) const;
        bool is_congr_root(expr const & e) const;
        bool check_invariant() const;
        bool inconsistent() const { return m_inconsistent; }
        bool in_singleton_eqc(expr const & e) const;
        bool in_heterogeneous_eqc(expr const & e) const;
        format pp_eqc(formatter const & fmt, expr const & e) const;
        format pp_eqcs(formatter const & fmt, bool nonsingleton_only = true) const;
        format pp_parent_occs(formatter const & fmt, expr const & e) const;
        format pp_parent_occs(formatter const & fmt) const;
        unsigned get_gmt() const { return m_gmt; }
        void inc_gmt() { m_gmt++; }
        config const & get_config() const { return m_config; }
        vm_obj mk_vm_cc_config() const;
    };

private:
    type_context_old &            m_ctx;
    defeq_canonizer           m_defeq_canonizer;
    state &                   m_state;
    buffer<todo_entry>        m_todo;
    ext_congr_lemma_cache_ptr m_cache_ptr;
    transparency_mode         m_mode;
    relation_info_getter      m_rel_info_getter;
    symm_info_getter          m_symm_info_getter;
    refl_info_getter          m_refl_info_getter;
    theory_ac                 m_ac;
    cc_propagation_handler *  m_phandler;
    cc_normalizer *           m_normalizer;
    friend class theory_ac;

    bool compare_symm(expr lhs1, expr rhs1, expr lhs2, expr rhs2) const;
    bool compare_symm(pair<expr, name> const & k1, pair<expr, name> const & k2) const;
    unsigned mk_symm_hash(expr const & lhs, expr const & rhs) const;
    optional<name> is_binary_relation(expr const & e, expr & lhs, expr & rhs) const;
    optional<name> is_symm_relation(expr const & e, expr & lhs, expr & rhs) const;
    optional<name> is_refl_relation(expr const & e, expr & lhs, expr & rhs) const;
    bool is_symm_relation(expr const & e);
    unsigned mk_congr_hash(expr const & e) const;
    bool is_congruent(expr const & e1, expr const & e2) const;
    void set_fo(expr const & e);
    bool is_value(expr const & e);
    bool is_interpreted_value(expr const & e);
    void process_subsingleton_elem(expr const & e);
    void apply_simple_eqvs(expr const & e);
    void add_occurrence(expr const & parent, expr const & child, bool symm_table);
    void add_congruence_table(expr const & e);
    void check_eq_true(expr const & e);
    void add_symm_congruence_table(expr const & e);
    void mk_entry(expr const & e, bool interpreted, unsigned gen);
    void set_ac_var(expr const & e);
    void internalize_app(expr const & e, unsigned gen);
    void internalize_core(expr const & e, optional<expr> const & parent, unsigned gen);
    void push_todo(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof);
    void push_heq(expr const & lhs, expr const & rhs, expr const & H);
    void push_eq(expr const & lhs, expr const & rhs, expr const & H);
    void push_refl_eq(expr const & lhs, expr const & rhs);
    void invert_trans(expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof);
    void invert_trans(expr const & e);
    void remove_parents(expr const & e, buffer<expr> & parents_to_propagate);
    void reinsert_parents(expr const & e);
    void update_mt(expr const & e);
    bool has_heq_proofs(expr const & root) const;
    expr flip_proof_core(expr const & H, bool flipped, bool heq_proofs) const;
    expr flip_proof(expr const & H, bool flipped, bool heq_proofs) const;
    optional<ext_congr_lemma> mk_ext_hcongr_lemma(expr const & fn, unsigned nargs) const;
    expr mk_trans(expr const & H1, expr const & H2, bool heq_proofs) const;
    expr mk_trans(optional<expr> const & H1, expr const & H2, bool heq_proofs) const;
    expr mk_congr_proof_core(expr const & e1, expr const & e2, bool heq_proofs) const;
    optional<expr> mk_symm_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const;
    expr mk_congr_proof(expr const & lhs, expr const & rhs, bool heq_proofs) const;
    expr mk_proof(expr const & lhs, expr const & rhs, expr const & H, bool heq_proofs) const;
    optional<expr> get_eq_proof_core(expr const & e1, expr const & e2, bool as_heq) const;
    void push_subsingleton_eq(expr const & a, expr const & b);
    void check_new_subsingleton_eq(expr const & old_root, expr const & new_root);
    bool is_eq_true(expr const & e) const;
    bool is_eq_false(expr const & e) const;
    expr get_eq_true_proof(expr const & e) const;
    expr get_eq_false_proof(expr const & e) const;
    expr get_prop_eq_proof(expr const & a, expr const & b) const;
    static bool may_propagate(expr const & e);
    void propagate_iff_up(expr const & e);
    void propagate_and_up(expr const & e);
    void propagate_or_up(expr const & e);
    void propagate_not_up(expr const & e);
    void propagate_imp_up(expr const & e);
    void propagate_ite_up(expr const & e);
    optional<expr> mk_ne_of_eq_of_ne(expr const & a, expr const & a1, expr const & a1_ne_b);
    optional<expr> mk_ne_of_ne_of_eq(expr const & a_ne_b1, expr const & b1, expr const & b);
    void propagate_eq_up(expr const & e);
    void propagate_up(expr const & e);
    void propagate_and_down(expr const & e);
    void propagate_or_down(expr const & e);
    void propagate_not_down(expr const & e);
    void propagate_eq_down(expr const & e);
    expr_pair to_forall_not(expr const & ex, expr const & h_not_ex);
    void propagate_exists_down(expr const & e);
    void propagate_down(expr const & e);
    void propagate_inst_implicit(expr const & e);
    void propagate_constructor_eq(expr const & e1, expr const & e2);
    void propagate_projection_constructor(expr const & p, expr const & c);
    void propagate_value_inconsistency(expr const & e1, expr const & e2);
    void get_eqc_lambdas(expr const & e, buffer<expr> & r);
    void propagate_beta(expr const & fn, buffer<expr> const & rev_args, buffer<expr> const & lambdas, buffer<expr> & r);
    void propagate_beta_to_eqc(buffer<expr> const & fn_roots, buffer<expr> const & lambdas, buffer<expr> & new_lambda_apps);
    void collect_fn_roots(expr const & root, buffer<expr> & fn_roots);
    void add_eqv_step(expr e1, expr e2, expr const & H, bool heq_proof);
    void process_todo();
    void add_eqv_core(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof);
    bool check_eqc(expr const & e) const;
    bool check_congr_keys() const;

    friend ext_congr_lemma_cache_ptr const & get_cache_ptr(congruence_closure const & cc);
public:
    congruence_closure(type_context_old & ctx, state & s, defeq_canonizer::state & dcs,
                       cc_propagation_handler * phandler = nullptr,
                       cc_normalizer * normalizer = nullptr);
    ~congruence_closure();

    environment const & env() const { return m_ctx.env(); }
    type_context_old & ctx() { return m_ctx; }
    transparency_mode mode() const { return m_mode; }
    defeq_canonizer & get_defeq_canonizer() { return m_defeq_canonizer; }

    /** \brief Register expression \c e in this data-structure.
       It creates entries for each sub-expression in \c e.
       It also updates the m_parents mapping.

       We ignore the following subterms of \c e.
       1- and, or and not-applications are not inserted into the data-structures, but
          their arguments are visited.
       2- (Pi (x : A), B), the subterms A and B are not visited if B depends on x.
       3- (A -> B) is not inserted into the data-structures, but their arguments are visited
          if they are propositions.
       4- Terms containing meta-variables.
       5- The subterms of lambda-expressions.
       6- Sorts (Type and Prop). */
    void internalize(expr const & e, unsigned gen);

    void add(expr const & type, expr const & proof, unsigned gen);

    bool is_eqv(expr const & e1, expr const & e2) const;
    bool is_not_eqv(expr const & e1, expr const & e2) const;
    bool proved(expr const & e) const;

    bool is_def_eq(expr const & e1, expr const & e2) const {
        return m_ctx.pure_is_def_eq(e1, e2);
    }

    bool relaxed_is_def_eq(expr const & e1, expr const & e2) const {
        return m_ctx.pure_relaxed_is_def_eq(e1, e2);
    }

    expr get_root(expr const & e) const { return m_state.get_root(e); }
    expr get_next(expr const & e) const { return m_state.get_next(e); }
    bool is_congr_root(expr const & e) const { return m_state.is_congr_root(e); }
    bool in_heterogeneous_eqc(expr const & e) const { return m_state.in_heterogeneous_eqc(e); }

    optional<expr> get_heq_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_eq_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_inconsistency_proof() const;
    bool inconsistent() const { return m_state.inconsistent(); }

    unsigned get_gmt() const { return m_state.get_gmt(); }
    unsigned get_mt(expr const & t) const { return m_state.get_mt(t); }
    void inc_gmt() { m_state.inc_gmt(); }

    optional<ext_congr_lemma> mk_ext_congr_lemma(expr const & e) const;

    optional<expr> is_ac(expr const & e) {
        if (m_state.m_config.m_ac) return m_ac.is_ac(e);
        else return none_expr();
    }

    entry const * get_entry(expr const & e) const { return m_state.m_entries.find(e); }
    bool check_invariant() const { return m_state.check_invariant(); }

    expr normalize(expr const & e);

    unsigned get_generation_of(expr const & e) const {
        if (auto it = get_entry(e))
            return it->m_generation;
        else
            return 0;
    }

    class state_scope {
        congruence_closure & m_cc;
        state                m_saved_state;
    public:
        state_scope(congruence_closure & cc):m_cc(cc), m_saved_state(cc.m_state) {}
        ~state_scope() { m_cc.m_state = m_saved_state; }
    };
};

typedef congruence_closure::state  cc_state;
typedef congruence_closure::config cc_config;

struct ext_congr_lemma {
    /* The basic congr_lemma object defined at congr_lemma_manager */
    congr_lemma          m_congr_lemma;
    /* If m_heq_result is true, then lemma is based on heterogeneous equality
       and the conclusion is a heterogeneous equality. */
    unsigned             m_heq_result:1;
    /* If m_heq_lemma is true, then lemma was created using mk_hcongr_lemma. */
    unsigned             m_hcongr_lemma:1;
    ext_congr_lemma(congr_lemma const & H):
        m_congr_lemma(H), m_heq_result(false), m_hcongr_lemma(false) {}
};

void initialize_congruence_closure();
void finalize_congruence_closure();
}
```

src/library/tactic/smt/congruence_closure.cpp:
```c++
namespace lean {
struct ext_congr_lemma_key {
    expr     m_fn;
    unsigned m_nargs;
    unsigned m_hash;
    ext_congr_lemma_key():m_nargs(0), m_hash(0) {}
    ext_congr_lemma_key(expr const & fn, unsigned nargs):
        m_fn(fn), m_nargs(nargs),
        m_hash(hash(fn.hash(), nargs)) {}
};

struct ext_congr_lemma_key_hash_fn {
    unsigned operator()(ext_congr_lemma_key const & k) const { return k.m_hash; }
};

struct ext_congr_lemma_key_eq_fn {
    bool operator()(ext_congr_lemma_key const & k1, ext_congr_lemma_key const & k2) const {
        return k1.m_fn == k2.m_fn && k1.m_nargs == k2.m_nargs;
    }
};

typedef std::unordered_map<ext_congr_lemma_key,
                           optional<ext_congr_lemma>,
                           ext_congr_lemma_key_hash_fn,
                           ext_congr_lemma_key_eq_fn> ext_congr_lemma_cache_data;

struct ext_congr_lemma_cache {
    environment                m_env;
    ext_congr_lemma_cache_data m_cache[LEAN_NUM_TRANSPARENCY_MODES];

    ext_congr_lemma_cache(environment const & env):m_env(env) {
    }
};

typedef std::shared_ptr<ext_congr_lemma_cache> ext_congr_lemma_cache_ptr;

congruence_closure::congruence_closure(type_context_old & ctx, state & s, defeq_canonizer::state & dcs,
                                       cc_propagation_handler * phandler,
                                       cc_normalizer * normalizer):
    m_ctx(ctx), m_defeq_canonizer(ctx, dcs), m_state(s), m_cache_ptr(std::make_shared<ext_congr_lemma_cache>(ctx.env())), m_mode(ctx.mode()),
    m_rel_info_getter(mk_relation_info_getter(ctx.env())),
    m_symm_info_getter(mk_symm_info_getter(ctx.env())),
    m_refl_info_getter(mk_refl_info_getter(ctx.env())),
    m_ac(*this, m_state.m_ac_state),
    m_phandler(phandler),
    m_normalizer(normalizer) {
}

congruence_closure::~congruence_closure() {
}

inline ext_congr_lemma_cache_ptr const & get_cache_ptr(congruence_closure const & cc) {
    return cc.m_cache_ptr;
}

inline ext_congr_lemma_cache_data & get_cache(congruence_closure const & cc) {
    return get_cache_ptr(cc)->m_cache[static_cast<unsigned>(cc.mode())];
}

/* Automatically generated congruence lemma based on heterogeneous equality. */
static optional<ext_congr_lemma> mk_hcongr_lemma_core(type_context_old & ctx, expr const & fn, unsigned nargs) {
    optional<congr_lemma> eq_congr = mk_hcongr(ctx, fn, nargs);
    if (!eq_congr) return optional<ext_congr_lemma>();
    ext_congr_lemma res1(*eq_congr);
    expr type = eq_congr->get_type();
    while (is_pi(type)) type = binding_body(type);
    lean_assert(is_eq(type) || is_heq(type));
    res1.m_hcongr_lemma = true;
    if (is_heq(type))
        res1.m_heq_result = true;
    return optional<ext_congr_lemma>(res1);
}

optional<ext_congr_lemma> congruence_closure::mk_ext_hcongr_lemma(expr const & fn, unsigned nargs) const {
    auto & cache = get_cache(*this);
    ext_congr_lemma_key key1(fn, nargs);
    auto it1 = cache.find(key1);
    if (it1 != cache.end())
        return it1->second;

    if (auto lemma = mk_hcongr_lemma_core(m_ctx, fn, nargs)) {
        /* succeeded */
        cache.insert(mk_pair(key1, lemma));
        return lemma;
    }

    /* cache failure */
    cache.insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

optional<ext_congr_lemma> congruence_closure::mk_ext_congr_lemma(expr const & e) const {
    expr const & fn     = get_app_fn(e);
    unsigned nargs      = get_app_num_args(e);
    auto & cache        = get_cache(*this);

    /* Check if (fn, nargs) is in the cache */
    ext_congr_lemma_key key1(fn, nargs);
    auto it1 = cache.find(key1);
    if (it1 != cache.end())
        return it1->second;

    /* Try automatically generated congruence lemma with support for heterogeneous equality. */
    auto lemma = mk_hcongr_lemma_core(m_ctx, fn, nargs);

    if (lemma) {
        /* succeeded */
        cache.insert(mk_pair(key1, lemma));
        return lemma;
    }

    /* cache failure */
    cache.insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

expr congruence_closure::state::get_root(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_root;
    } else {
        return e;
    }
}

void congruence_closure::state::get_roots(buffer<expr> & roots, bool nonsingleton_only) const {
    m_entries.for_each([&](expr const & k, entry const & n) {
            if (k == n.m_root && (!nonsingleton_only || !in_singleton_eqc(k)))
                roots.push_back(k);
        });
}

expr congruence_closure::state::get_next(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_next;
    } else {
        return e;
    }
}

unsigned congruence_closure::state::get_mt(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_mt;
    } else {
        return m_gmt;
    }
}

bool congruence_closure::state::is_congr_root(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return e == n->m_cg_root;
    } else {
        return true;
    }
}

bool congruence_closure::state::in_heterogeneous_eqc(expr const & e) const {
    if (auto n = m_entries.find(get_root(e)))
        return n->m_heq_proofs;
    else
        return false;
}

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
(em               : bool)
 */
vm_obj congruence_closure::state::mk_vm_cc_config() const {
    vm_obj ho_fns;
    if (get_config().m_all_ho) {
        ho_fns = mk_vm_none();
    } else {
        buffer<name> fns;
        m_ho_fns.to_buffer(fns);
        ho_fns = mk_vm_some(to_obj(fns));
    }
    vm_obj ignore_instances = mk_vm_bool(get_config().m_ignore_instances);
    vm_obj ac               = mk_vm_bool(get_config().m_ac);
    vm_obj em               = mk_vm_bool(get_config().m_em);
    return mk_vm_constructor(0, ignore_instances, ac, ho_fns, em);
}

/** \brief Return true iff the given function application are congruent

    See paper: Congruence Closure for Intensional Type Theory. */
bool congruence_closure::is_congruent(expr const & e1, expr const & e2) const {
    lean_assert(is_app(e1) && is_app(e2));
    if (get_entry(e1)->m_fo) {
        buffer<expr> args1, args2;
        expr const & f1 = get_app_args(e1, args1);
        expr const & f2 = get_app_args(e2, args2);
        if (args1.size() != args2.size()) return false;
        for (unsigned i = 0; i < args1.size(); i++) {
            if (get_root(args1[i]) != get_root(args2[i]))
                return false;
        }
        if (f1 == f2) return true;
        if (get_root(f1) != get_root(f2)) {
            /* f1 and f2 are not equivalent */
            return false;
        }
        if (is_def_eq(m_ctx.infer(f1), m_ctx.infer(f2))) {
            /* f1 and f2 have the same type, then we can create a congruence proof for e1 == e2 */
            return true;
        }
        return false;
    } else {
        /* Given e1 := f a,  e2 := g b */
        expr f = app_fn(e1);
        expr a = app_arg(e1);
        expr g = app_fn(e2);
        expr b = app_arg(e2);
        if (get_root(a) != get_root(b)) {
            /* a and b are not equivalent */
            return false;
        }
        if (get_root(f) != get_root(g)) {
            /* f and g are not equivalent */
            return false;
        }
        if (is_def_eq(m_ctx.infer(f), m_ctx.infer(g))) {
            /* Case 1: f and g have the same type, then we can create a congruence proof for f a == g b */
            return true;
        }
        if (is_app(f) && is_app(g)) {
            /* Case 2: f and g are congruent */
            return is_congruent(f, g);
        }
        /*
        f and g are not congruent nor they have the same type.
        We can't generate a congruence proof in this case because the following lemma

            hcongr : f1 == f2 -> a1 == a2 -> f1 a1 == f2 a2

        is not provable. Remark: it is also not provable in MLTT, Coq and Agda (even if we assume UIP). */
        return false;
    }
}

/* Auxiliary function for comparing (lhs1 ~ rhs1) and (lhs2 ~ rhs2),
   when ~ is symmetric/commutative.
   It returns true (equal) for (a ~ b) (b ~ a) */
bool congruence_closure::compare_symm(expr lhs1, expr rhs1, expr lhs2, expr rhs2) const {
    lhs1 = get_root(lhs1);
    rhs1 = get_root(rhs1);
    lhs2 = get_root(lhs2);
    rhs2 = get_root(rhs2);
    if (is_lt(lhs1, rhs1, true))
        std::swap(lhs1, rhs1);
    if (is_lt(lhs2, rhs2, true))
        std::swap(lhs2, rhs2);
    return lhs1 == lhs2 && rhs1 == rhs2;
}

bool congruence_closure::compare_symm(pair<expr, name> const & k1, pair<expr, name> const & k2) const {
    if (k1.second != k2.second)
        return false;
    expr const & e1 = k1.first;
    expr const & e2 = k2.first;
    if (k1.second == get_eq_name() || k1.second == get_iff_name()) {
        return compare_symm(app_arg(app_fn(e1)), app_arg(e1), app_arg(app_fn(e2)), app_arg(e2));
    } else {
        expr lhs1, rhs1, lhs2, rhs2;
        is_symm_relation(e1, lhs1, rhs1);
        is_symm_relation(e2, lhs2, rhs2);
        return compare_symm(lhs1, rhs1, lhs2, rhs2);
    }
}

unsigned congruence_closure::mk_symm_hash(expr const & lhs, expr const & rhs) const {
    unsigned h1 = get_root(lhs).hash();
    unsigned h2 = get_root(rhs).hash();
    if (h1 > h2)
        std::swap(h1, h2);
    return (h1 << 16) | (h2 & 0xFFFF);
}

unsigned congruence_closure::mk_congr_hash(expr const & e) const {
    lean_assert(is_app(e));
    unsigned h;
    if (get_entry(e)->m_fo) {
        /* first-order case, where we do not consider all partial applications */
        h = get_root(app_arg(e)).hash();
        expr const * it = &(app_fn(e));
        while (is_app(*it)) {
            h  = hash(h, get_root(app_arg(*it)).hash());
            it = &app_fn(*it);
        }
        h = hash(h, get_root(*it).hash());
    } else {
        expr const & f = app_fn(e);
        expr const & a = app_arg(e);
        h = hash(get_root(f).hash(), get_root(a).hash());
    }
    return h;
}

optional<name> congruence_closure::is_binary_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (!is_app(e)) return optional<name>();
    expr fn = get_app_fn(e);
    if (!is_constant(fn)) return optional<name>();
    if (auto info = m_rel_info_getter(const_name(fn))) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() != info->get_arity()) return optional<name>();
        lhs = args[info->get_lhs_pos()];
        rhs = args[info->get_rhs_pos()];
        return optional<name>(const_name(fn));
    }
    return optional<name>();
}

optional<name> congruence_closure::is_symm_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (is_eq(e, lhs, rhs)) {
        return optional<name>(get_eq_name());
    } else if (is_iff(e, lhs, rhs)) {
        return optional<name>(get_iff_name());
    } else if (auto r = is_binary_relation(e, lhs, rhs)) {
        if (!m_symm_info_getter(const_name(get_app_fn(e)))) return optional<name>();
        return r;
    }
    return optional<name>();
}

optional<name> congruence_closure::is_refl_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (is_eq(e, lhs, rhs)) {
        return optional<name>(get_eq_name());
    } else if (is_iff(e, lhs, rhs)) {
        return optional<name>(get_iff_name());
    } else if (auto r = is_binary_relation(e, lhs, rhs)) {
        if (!m_refl_info_getter(const_name(get_app_fn(e)))) return optional<name>();
        return r;
    }
    return optional<name>();
}

bool congruence_closure::is_symm_relation(expr const & e) {
    expr lhs, rhs;
    return static_cast<bool>(is_symm_relation(e, lhs, rhs));
}

void congruence_closure::push_todo(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof) {
    m_todo.emplace_back(lhs, rhs, H, heq_proof);
}

void congruence_closure::push_heq(expr const & lhs, expr const & rhs, expr const & H) {
    m_todo.emplace_back(lhs, rhs, H, true);
}

void congruence_closure::push_eq(expr const & lhs, expr const & rhs, expr const & H) {
    m_todo.emplace_back(lhs, rhs, H, false);
}

expr congruence_closure::normalize(expr const & e) {
    if (m_normalizer)
        return m_normalizer->normalize(e);
    else
        return e;
}

void congruence_closure::process_subsingleton_elem(expr const & e) {
    expr type = m_ctx.infer(e);
    optional<expr> ss = m_ctx.mk_subsingleton_instance(type);
    if (!ss) return; /* type is not a subsingleton */
    type = normalize(type);
    /* Make sure type has been internalized */
    internalize_core(type, none_expr(), get_generation_of(e));
    /* Try to find representative */
    if (auto it = m_state.m_subsingleton_reprs.find(type)) {
        push_subsingleton_eq(e, *it);
    } else {
        m_state.m_subsingleton_reprs.insert(type, e);
    }
    expr type_root     = get_root(type);
    if (type_root == type)
        return;
    if (auto it2 = m_state.m_subsingleton_reprs.find(type_root)) {
        push_subsingleton_eq(e, *it2);
    } else {
        m_state.m_subsingleton_reprs.insert(type_root, e);
    }
}

/* This method is invoked during internalization and eagerly apply basic equivalences for term \c e
   Examples:
   - If e := cast H e', then it merges the equivalence classes of (cast H e') and e'

   In principle, we could mark theorems such as cast_eq as simplification rules, but this creates
   problems with the builtin support for cast-introduction in the ematching module.

   Eagerly merging the equivalence classes is also more efficient. */
void congruence_closure::apply_simple_eqvs(expr const & e) {
    if (is_app_of(e, get_cast_name(), 4)) {
        /* cast H a == a

           theorem cast_heq : ∀ {A B : Type.{l_1}} (H : A = B) (a : A), @cast.{l_1} A B H a == a
        */
        buffer<expr> args;
        expr const & cast = get_app_args(e, args);
        expr const & a    = args[3];
        expr proof        = mk_app(mk_constant(get_cast_heq_name(), const_levels(cast)), args);
        push_heq(e, a, proof);
    }

    if (is_app_of(e, get_eq_rec_name(), 6)) {
        /* eq.rec p H == p

           theorem eq_rec_heq : ∀ {A : Type.{l_1}} {P : A → Type.{l_2}} {a a' : A} (H : a = a') (p : P a), @eq.rec.{l_2 l_1} A a P p a' H == p
        */
        buffer<expr> args;
        expr const & eq_rec = get_app_args(e, args);
        expr A = args[0]; expr a = args[1]; expr P = args[2]; expr p = args[3];
        expr a_prime = args[4]; expr H = args[5];
        level l_2  = head(const_levels(eq_rec));
        level l_1  = head(tail(const_levels(eq_rec)));
        expr proof = mk_app({mk_constant(get_eq_rec_heq_name(), {l_1, l_2}), A, P, a, a_prime, H, p});
        push_heq(e, p, proof);
    }

    if (is_app_of(e, get_ne_name(), 3)) {
        /* (a ≠ b) = (not (a = b)) */
        expr const & a = app_arg(app_fn(e));
        expr const & b = app_arg(e);
        expr new_e     = mk_not(mk_eq(m_ctx, a, b));
        internalize_core(new_e, none_expr(), get_generation_of(e));
        push_refl_eq(e, new_e);
    }

    if (auto r = m_ctx.reduce_projection(e)) {
        push_refl_eq(e, *r);
    }

    expr const & fn = get_app_fn(e);
    if (is_lambda(fn)) {
        expr reduced_e = head_beta_reduce(e);
        if (m_phandler)
            m_phandler->new_aux_cc_term(reduced_e);
        internalize_core(reduced_e, none_expr(), get_generation_of(e));
        push_refl_eq(e, reduced_e);
    }

    buffer<expr> rev_args;
    auto it = e;
    while (is_app(it)) {
        rev_args.push_back(app_arg(it));
        expr const & fn = app_fn(it);
        expr root_fn  = get_root(fn);
        auto en = get_entry(root_fn);
        if (en && en->m_has_lambdas) {
            buffer<expr> lambdas;
            get_eqc_lambdas(root_fn, lambdas);
            buffer<expr> new_lambda_apps;
            propagate_beta(fn, rev_args, lambdas, new_lambda_apps);
            for (expr const & new_app : new_lambda_apps) {
                internalize_core(new_app, none_expr(), get_generation_of(e));
            }
        }
        it = fn;
    }

    propagate_up(e);
}

void congruence_closure::add_occurrence(expr const & parent, expr const & child, bool symm_table) {
    parent_occ_set ps;
    expr child_root = get_root(child);
    if (auto old_ps = m_state.m_parents.find(child_root))
        ps = *old_ps;
    ps.insert(parent_occ(parent, symm_table));
    m_state.m_parents.insert(child_root, ps);
}

static expr * g_congr_mark   = nullptr; // dummy congruence proof, it is just a placeholder.
static expr * g_eq_true_mark = nullptr; // dummy eq_true proof, it is just a placeholder.
static expr * g_refl_mark    = nullptr; // dummy refl proof, it is just a placeholder.

void congruence_closure::push_refl_eq(expr const & lhs, expr const & rhs) {
    m_todo.emplace_back(lhs, rhs, *g_refl_mark, false);
}

void congruence_closure::add_congruence_table(expr const & e) {
    lean_assert(is_app(e));
    unsigned h = mk_congr_hash(e);
    if (list<expr> const * es = m_state.m_congruences.find(h)) {
        for (expr const & old_e : *es) {
            if (is_congruent(e, old_e)) {
                /*
                  Found new equivalence: e ~ old_e
                  1. Update m_cg_root field for e
                */
                entry new_entry     = *get_entry(e);
                new_entry.m_cg_root = old_e;
                m_state.m_entries.insert(e, new_entry);
                /* 2. Put new equivalence in the todo queue */
                /* TODO(Leo): check if the following line is a bottleneck */
                bool heq_proof = !is_def_eq(m_ctx.infer(e), m_ctx.infer(old_e));
                push_todo(e, old_e, *g_congr_mark, heq_proof);
                return;
            }
        }
        m_state.m_congruences.insert(h, cons(e, *es));
    } else {
        m_state.m_congruences.insert(h, to_list(e));
    }
}

void congruence_closure::check_eq_true(expr const & e) {
    expr lhs, rhs;
    if (!is_refl_relation(e, lhs, rhs))
        return;
    if (is_eqv(e, mk_true()))
        return; // it is already equivalent to true
    lhs = get_root(lhs);
    rhs = get_root(rhs);
    if (lhs != rhs) return;
    // Add e = true
    push_eq(e, mk_true(), *g_eq_true_mark);
}

void congruence_closure::add_symm_congruence_table(expr const & e) {
    lean_assert(is_symm_relation(e));
    expr lhs, rhs;
    auto rel = is_symm_relation(e, lhs, rhs);
    lean_assert(rel);
    unsigned h = mk_symm_hash(lhs, rhs);
    pair<expr, name> new_p(e, *rel);
    if (list<pair<expr, name>> const * ps = m_state.m_symm_congruences.find(h)) {
        for (pair<expr, name> const & p : *ps) {
            if (compare_symm(new_p, p)) {
                /*
                  Found new equivalence: e ~ p.first
                  1. Update m_cg_root field for e
                */
                entry new_entry     = *get_entry(e);
                new_entry.m_cg_root = p.first;
                m_state.m_entries.insert(e, new_entry);
                /* 2. Put new equivalence in the TODO queue */
                // NOTE(gabriel): support for symmetric relations is pretty much broken,
                // since it ignores all arguments except the last two ones.
                // e.g. this would claim that `modeq n a b` and `modeq m a b` are equivalent.
                // Whitelist some relations to contain breakage:
                if (*rel == get_eq_name() || get_app_num_args(e) == 2)
                    push_eq(e, p.first, *g_congr_mark);
                check_eq_true(e);
                return;
            }
        }
        m_state.m_symm_congruences.insert(h, cons(new_p, *ps));
        check_eq_true(e);
    } else {
        m_state.m_symm_congruences.insert(h, to_list(new_p));
        check_eq_true(e);
    }
}

congruence_closure::state::state(name_set const & ho_fns, config const & cfg):
    m_ho_fns(ho_fns), m_config(cfg) {
    bool interpreted = true;
    bool constructor = false;
    unsigned gen     = 0;
    mk_entry_core(mk_true(), interpreted, constructor, gen);
    mk_entry_core(mk_false(), interpreted, constructor, gen);
}

void congruence_closure::state::mk_entry_core(expr const & e, bool interpreted, bool constructor, unsigned gen) {
    lean_assert(m_entries.find(e) == nullptr);
    entry n;
    n.m_next         = e;
    n.m_root         = e;
    n.m_cg_root      = e;
    n.m_size         = 1;
    n.m_flipped      = false;
    n.m_interpreted  = interpreted;
    n.m_constructor  = constructor;
    n.m_has_lambdas  = is_lambda(e);
    n.m_heq_proofs   = false;
    n.m_mt           = m_gmt;
    n.m_fo           = false;
    n.m_generation   = gen;
    m_entries.insert(e, n);
}

void congruence_closure::mk_entry(expr const & e, bool interpreted, unsigned gen) {
    if (get_entry(e)) return;
    bool constructor = static_cast<bool>(is_constructor_app(env(), e));
    m_state.mk_entry_core(e, interpreted, constructor, gen);
    process_subsingleton_elem(e);
}

/** Return true if 'e' represents a value (numeral, character, or string).
    TODO(Leo): move this code to a different place. */
bool congruence_closure::is_value(expr const & e) {
    return is_signed_num(e) || is_char_value(m_ctx, e) || is_string_value(e);
}

/** Return true if 'e' represents a value (nat/int numereal, character, or string).
    TODO(Leo): move this code to a different place. */
bool congruence_closure::is_interpreted_value(expr const & e) {
    if (is_string_value(e))
        return true;
    if (is_char_value(m_ctx, e))
        return true;
    if (is_signed_num(e)) {
        expr type = m_ctx.infer(e);
        return is_def_eq(type, mk_nat_type()) || is_def_eq(type, mk_int_type());
    }
    return false;
}

/** Given (f a b c), store in r, (f a), (f a b), (f a b c), and return f.
    Remark: this procedure is very similar to get_app_args.
    TODO(Leo): move this code to a differen place. */
static expr const & get_app_apps(expr const & e, buffer<expr> & r) {
    unsigned sz = r.size();
    expr const * it = &e;
    while (is_app(*it)) {
        r.push_back(*it);
        it = &(app_fn(*it));
    }
    std::reverse(r.begin() + sz, r.end());
    return *it;
}

void congruence_closure::propagate_inst_implicit(expr const & e) {
    bool updated;
    expr new_e = m_defeq_canonizer.canonize(e, updated);
    if (e != new_e) {
        mk_entry(new_e, false, get_generation_of(e));
        push_refl_eq(e, new_e);
    }
}

void congruence_closure::set_ac_var(expr const & e) {
    expr e_root = get_root(e);
    auto root_entry = get_entry(e_root);
    if (root_entry->m_ac_var) {
        m_ac.add_eq(*root_entry->m_ac_var, e);
    } else {
        entry new_root_entry = *root_entry;
        new_root_entry.m_ac_var = some_expr(e);
        m_state.m_entries.insert(e_root, new_root_entry);
    }
}

void congruence_closure::internalize_app(expr const & e, unsigned gen) {
    if (is_interpreted_value(e)) {
        bool interpreted = true;
        mk_entry(e, interpreted, gen);
        if (m_state.m_config.m_values) {
            /* we treat values as atomic symbols */
            return;
        }
    } else {
        bool interpreted = false;
        mk_entry(e, interpreted, gen);
        if (m_state.m_config.m_values && is_value(e)) {
            /* we treat values as atomic symbols */
            return;
        }
    }

    expr lhs, rhs;
    if (is_symm_relation(e, lhs, rhs)) {
        internalize_core(lhs, some_expr(e), gen);
        internalize_core(rhs, some_expr(e), gen);
        bool symm_table = true;
        add_occurrence(e, lhs, symm_table);
        add_occurrence(e, rhs, symm_table);
        add_symm_congruence_table(e);
    } else if (auto lemma = mk_ext_congr_lemma(e)) {
        bool symm_table = false;
        buffer<expr> apps;
        expr const & fn = get_app_apps(e, apps);
        lean_assert(apps.size() > 0);
        lean_assert(apps.back() == e);
        list<param_info> pinfos;
        if (m_state.m_config.m_ignore_instances)
            pinfos = get_fun_info(m_ctx, fn, apps.size()).get_params_info();
        if (!m_state.m_config.m_all_ho && is_constant(fn) && !m_state.m_ho_fns.contains(const_name(fn))) {
            for (unsigned i = 0; i < apps.size(); i++) {
                expr const & arg = app_arg(apps[i]);
                add_occurrence(e, arg, symm_table);
                if (pinfos && head(pinfos).is_inst_implicit()) {
                    /* We do not recurse on instances when m_state.m_config.m_ignore_instances is true. */
                    bool interpreted = false;
                    mk_entry(arg, interpreted, gen);
                    propagate_inst_implicit(arg);
                } else {
                    internalize_core(arg, some_expr(e), gen);
                }
                if (pinfos) pinfos = tail(pinfos);
            }
            internalize_core(fn, some_expr(e), gen);
            add_occurrence(e, fn, symm_table);
            set_fo(e);
            add_congruence_table(e);
        } else {
            /* Expensive case where we store a quadratic number of occurrences,
               as described in the paper "Congruence Closure in Internsional Type Theory" */
            for (unsigned i = 0; i < apps.size(); i++) {
                expr const & curr = apps[i];
                lean_assert(is_app(curr));
                expr const & curr_arg  = app_arg(curr);
                expr const & curr_fn   = app_fn(curr);
                if (i < apps.size() - 1) {
                    bool interpreted = false;
                    mk_entry(curr, interpreted, gen);
                }
                for (unsigned j = i; j < apps.size(); j++) {
                    add_occurrence(apps[j], curr_arg, symm_table);
                    add_occurrence(apps[j], curr_fn, symm_table);
                }
                if (pinfos && head(pinfos).is_inst_implicit()) {
                    /* We do not recurse on instances when m_state.m_config.m_ignore_instances is true. */
                    bool interpreted = false;
                    mk_entry(curr_arg, interpreted, gen);
                    mk_entry(curr_fn, interpreted, gen);
                    propagate_inst_implicit(curr_arg);
                } else {
                    internalize_core(curr_arg, some_expr(e), gen);
                    bool interpreted = false;
                    mk_entry(curr_fn, interpreted, gen);
                }
                if (pinfos) pinfos = tail(pinfos);
                add_congruence_table(curr);
            }
        }
    }
    apply_simple_eqvs(e);
}

void congruence_closure::internalize_core(expr const & e, optional<expr> const & parent, unsigned gen) {
    lean_assert(closed(e));
    /* We allow metavariables after partitions have been frozen. */
    if (has_expr_metavar(e) && !m_state.m_froze_partitions)
        return;
    /* Check whether 'e' has already been internalized. */
    if (!get_entry(e)) {
        switch (e.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:
            break;
        case expr_kind::Constant:
        case expr_kind::Meta:
            mk_entry(e, false, gen);
            break;
        case expr_kind::Lambda:
        case expr_kind::Let:
            mk_entry(e, false, gen);
            break;
        case expr_kind::Local:
            mk_entry(e, false, gen);
            if (is_local_decl_ref(e)) {
                if (auto d = m_ctx.lctx().find_local_decl(e)) {
                    if (auto v = d->get_value()) {
                        push_refl_eq(e, *v);
                    }
                }
            }
            break;
        case expr_kind::Macro:
            if (is_interpreted_value(e)) {
                bool interpreted = true;
                mk_entry(e, interpreted, gen);
            } else {
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    internalize_core(macro_arg(e, i), some_expr(e), gen);
                bool interpreted = false;
                mk_entry(e, interpreted, gen);
                if (is_annotation(e))
                    push_refl_eq(e, get_annotation_arg(e));
            }
            break;
        case expr_kind::Pi:
            if (is_arrow(e) && m_ctx.is_prop(binding_domain(e)) && m_ctx.is_prop(binding_body(e))) {
                internalize_core(binding_domain(e), some_expr(e), gen);
                internalize_core(binding_body(e), some_expr(e), gen);
                bool symm_table = false;
                add_occurrence(e, binding_domain(e), symm_table);
                add_occurrence(e, binding_body(e), symm_table);
                propagate_imp_up(e);
            }
            if (m_ctx.is_prop(e)) {
                mk_entry(e, false, gen);
            }
            break;
        case expr_kind::App: {
            internalize_app(e, gen);
            break;
        }}
    }

    /* Remark: if should invoke m_ac.internalize even if the test !get_entry(e) above failed.
       Reason, the first time e was visited, it may have been visited with a different parent. */
    if (m_state.m_config.m_ac)
        m_ac.internalize(e, parent);
}

/*
  The fields m_target and m_proof in e's entry are encoding a transitivity proof
  Let target(e) and proof(e) denote these fields.

  e    = target(e)           :  proof(e)
   ... = target(target(e))   :  proof(target(e))
   ... ...
       = root(e)             : ...

  The transitivity proof eventually reaches the root of the equivalence class.
  This method "inverts" the proof. That is, the m_target goes from root(e) to e after
  we execute it.
*/
void congruence_closure::invert_trans(expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof) {
    auto n = get_entry(e);
    lean_assert(n);
    entry new_n = *n;
    if (n->m_target)
        invert_trans(*new_n.m_target, !new_n.m_flipped, some_expr(e), new_n.m_proof);
    new_n.m_target  = new_target;
    new_n.m_proof   = new_proof;
    new_n.m_flipped = new_flipped;
    m_state.m_entries.insert(e, new_n);
}

void congruence_closure::invert_trans(expr const & e) {
    invert_trans(e, false, none_expr(), none_expr());
}

void congruence_closure::remove_parents(expr const & e, buffer<expr> & parents_to_propagate) {
    auto ps = m_state.m_parents.find(e);
    if (!ps) return;
    ps->for_each([&](parent_occ const & pocc) {
            expr const & p = pocc.m_expr;
            lean_trace(name({"debug", "cc"}), scope_trace_env(m_ctx.env(), m_ctx); tout() << "remove parent: " << p << "\n";);
            if (may_propagate(p))
                parents_to_propagate.push_back(p);
            if (is_app(p)) {
                if (pocc.m_symm_table) {
                    expr lhs, rhs;
                    auto rel = is_symm_relation(p, lhs, rhs);
                    lean_assert(rel);
                    unsigned h = mk_symm_hash(lhs, rhs);
                    if (list<pair<expr, name>> const * lst = m_state.m_symm_congruences.find(h)) {
                        pair<expr, name> k(p, *rel);
                        list<pair<expr, name>> new_lst = filter(*lst, [&](pair<expr, name> const & k2) {
                                return !compare_symm(k, k2);
                            });
                        if (new_lst)
                            m_state.m_symm_congruences.insert(h, new_lst);
                        else
                            m_state.m_symm_congruences.erase(h);
                    }
                } else {
                    unsigned h = mk_congr_hash(p);
                    if (list<expr> const * es = m_state.m_congruences.find(h)) {
                        list<expr> new_es = remove(*es, p);
                        if (new_es)
                            m_state.m_congruences.insert(h, new_es);
                        else
                            m_state.m_congruences.erase(h);
                    }
                }
            }
        });
}

void congruence_closure::reinsert_parents(expr const & e) {
    auto ps = m_state.m_parents.find(e);
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            lean_trace(name({"debug", "cc"}), scope_trace_env(m_ctx.env(), m_ctx); tout() << "reinsert parent: " << p.m_expr << "\n";);
            if (is_app(p.m_expr)) {
                if (p.m_symm_table) {
                    add_symm_congruence_table(p.m_expr);
                } else {
                    add_congruence_table(p.m_expr);
                }
            }
        });
}

void congruence_closure::update_mt(expr const & e) {
    expr r  = get_root(e);
    auto ps = m_state.m_parents.find(r);
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            auto it = get_entry(p.m_expr);
            lean_assert(it);
            if (it->m_mt < m_state.m_gmt) {
                auto new_it = *it;
                new_it.m_mt = m_state.m_gmt;
                m_state.m_entries.insert(p.m_expr, new_it);
                update_mt(p.m_expr);
            }
        });
}

void congruence_closure::set_fo(expr const & e) {
    entry d = *get_entry(e);
    d.m_fo  = true;
    m_state.m_entries.insert(e, d);
}

bool congruence_closure::has_heq_proofs(expr const & root) const {
    lean_assert(get_entry(root));
    lean_assert(get_entry(root)->m_root == root);
    return get_entry(root)->m_heq_proofs;
}

expr congruence_closure::flip_proof_core(expr const & H, bool flipped, bool heq_proofs) const {
    expr new_H = H;
    if (heq_proofs && is_eq(m_ctx.relaxed_whnf(m_ctx.infer(new_H)))) {
        new_H = mk_heq_of_eq(m_ctx, new_H);
    }
    if (!flipped) {
        return new_H;
    } else {
        return heq_proofs ? mk_heq_symm(m_ctx, new_H) : mk_eq_symm(m_ctx, new_H);
    }
}

expr congruence_closure::flip_proof(expr const & H, bool flipped, bool heq_proofs) const {
    if (H == *g_congr_mark || H == *g_eq_true_mark || H == *g_refl_mark) {
        return H;
    } else if (is_cc_theory_proof(H)) {
        expr H1 = flip_proof_core(get_cc_theory_proof_arg(H), flipped, heq_proofs);
        return mark_cc_theory_proof(H1);
    } else {
        return flip_proof_core(H, flipped, heq_proofs);
    }
}

expr congruence_closure::mk_trans(expr const & H1, expr const & H2, bool heq_proofs) const {
    return heq_proofs ? mk_heq_trans(m_ctx, H1, H2) : mk_eq_trans(m_ctx, H1, H2);
}

expr congruence_closure::mk_trans(optional<expr> const & H1, expr const & H2, bool heq_proofs) const {
    if (!H1) return H2;
    return mk_trans(*H1, H2, heq_proofs);
}

expr congruence_closure::mk_congr_proof_core(expr const & lhs, expr const & rhs, bool heq_proofs) const {
    buffer<expr> lhs_args, rhs_args;
    expr const * lhs_it = &lhs;
    expr const * rhs_it = &rhs;
    if (lhs != rhs) {
        while (true) {
            lhs_args.push_back(app_arg(*lhs_it));
            rhs_args.push_back(app_arg(*rhs_it));
            lhs_it = &app_fn(*lhs_it);
            rhs_it = &app_fn(*rhs_it);
            if (*lhs_it == *rhs_it)
                break;
            if (is_def_eq(*lhs_it, *rhs_it))
                break;
            if (is_eqv(*lhs_it, *rhs_it) &&
                is_def_eq(m_ctx.infer(*lhs_it), m_ctx.infer(*rhs_it)))
                break;
        }
    }
    if (lhs_args.empty()) {
        if (heq_proofs)
            return mk_heq_refl(m_ctx, lhs);
        else
            return mk_eq_refl(m_ctx, lhs);
    }
    std::reverse(lhs_args.begin(), lhs_args.end());
    std::reverse(rhs_args.begin(), rhs_args.end());
    lean_assert(lhs_args.size() == rhs_args.size());
    expr const & lhs_fn = *lhs_it;
    expr const & rhs_fn = *rhs_it;
    lean_assert(is_eqv(lhs_fn, rhs_fn) || is_def_eq(lhs_fn, rhs_fn));
    lean_assert(is_def_eq(m_ctx.infer(lhs_fn), m_ctx.infer(rhs_fn)));
    /* Create proof for
          (lhs_fn lhs_args[0] ... lhs_args[n-1]) = (lhs_fn rhs_args[0] ... rhs_args[n-1])
       where
          n == lhs_args.size()
    */
    auto spec_lemma = mk_ext_hcongr_lemma(lhs_fn, lhs_args.size());
    lean_assert(spec_lemma);
    list<congr_arg_kind> const * kinds_it = &spec_lemma->m_congr_lemma.get_arg_kinds();
    buffer<expr> lemma_args;
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        lean_assert(kinds_it);
        lemma_args.push_back(lhs_args[i]);
        lemma_args.push_back(rhs_args[i]);
        if (head(*kinds_it) == congr_arg_kind::HEq) {
            lemma_args.push_back(*get_heq_proof(lhs_args[i], rhs_args[i]));
        } else {
            lean_assert(head(*kinds_it) == congr_arg_kind::Eq);
            lemma_args.push_back(*get_eq_proof(lhs_args[i], rhs_args[i]));
        }
        kinds_it = &(tail(*kinds_it));
    }
    expr r = mk_app(spec_lemma->m_congr_lemma.get_proof(), lemma_args);
    if (spec_lemma->m_heq_result && !heq_proofs)
        r = mk_eq_of_heq(m_ctx, r);
    else if (!spec_lemma->m_heq_result && heq_proofs)
        r = mk_heq_of_eq(m_ctx, r);
    if (is_def_eq(lhs_fn, rhs_fn))
        return r;
    /* Convert r into a proof of lhs = rhs using eq.rec and
       the proof that lhs_fn = rhs_fn */
    expr lhs_fn_eq_rhs_fn = *get_eq_proof(lhs_fn, rhs_fn);
    type_context_old::tmp_locals locals(m_ctx);
    expr x                = locals.push_local("_x", m_ctx.infer(lhs_fn));
    expr motive_rhs       = mk_app(x, rhs_args);
    expr motive           = heq_proofs ? mk_heq(m_ctx, lhs, motive_rhs) : mk_eq(m_ctx, lhs, motive_rhs);
    motive                = locals.mk_lambda(motive);
    return mk_eq_rec(m_ctx, motive, r, lhs_fn_eq_rhs_fn);
}

optional<expr> congruence_closure::mk_symm_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const {
    expr lhs1, rhs1, lhs2, rhs2;
    auto R1 = is_symm_relation(e1, lhs1, rhs1);
    if (!R1) return none_expr();
    auto R2 = is_symm_relation(e2, lhs2, rhs2);
    if (!R2 || *R1 != *R2) return none_expr();
    if (!is_eqv(lhs1, lhs2)) {
        lean_assert(is_eqv(lhs1, rhs2));
        /*
          We must apply symmetry.
          The symm congruence table is implicitly using symmetry.
          That is, we have
             e1 := lhs1 ~R1~ rhs1
          and
             e2 := lhs2 ~R1~ rhs2
          But,
          (lhs1 ~R1 ~rhs2) and (rhs1 ~R1~ lhs2)
        */
        /*
         Given e1 := lhs1 ~R1~ rhs1,
         create proof for
           (lhs1 ~R1~ rhs1) = (rhs1 ~R1~ lhs1)
        */
        expr new_e1 = mk_rel(m_ctx, *R1, rhs1, lhs1);
        type_context_old::tmp_locals locals(m_ctx);
        expr h1  = locals.push_local("_h1", e1);
        expr h2  = locals.push_local("_h2", new_e1);
        expr e1_iff_new_e1 = mk_app(m_ctx, get_iff_intro_name(),
                                    m_ctx.mk_lambda(h1, mk_symm(m_ctx, *R1, h1)),
                                    m_ctx.mk_lambda(h2, mk_symm(m_ctx, *R1, h2)));
        expr e1_eq_new_e1  = mk_propext(e1, new_e1, e1_iff_new_e1);
        expr new_e1_eq_e2  = mk_congr_proof_core(new_e1, e2, heq_proofs);
        if (heq_proofs)
            e1_eq_new_e1   = mk_heq_of_eq(m_ctx, e1_eq_new_e1);
        return some_expr(mk_trans(e1_eq_new_e1, new_e1_eq_e2, heq_proofs));
    }
    return none_expr();
}

expr congruence_closure::mk_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const {
    if (auto r = mk_symm_congr_proof(e1, e2, heq_proofs))
        return *r;
    else
        return mk_congr_proof_core(e1, e2, heq_proofs);
}

expr congruence_closure::mk_proof(expr const & lhs, expr const & rhs, expr const & H, bool heq_proofs) const {
    if (H == *g_congr_mark) {
        return mk_congr_proof(lhs, rhs, heq_proofs);
    } else if (H == *g_eq_true_mark) {
        bool flip;
        expr a, b;
        name R;
        if (lhs == mk_true()) {
            R = *is_refl_relation(rhs, a, b);
            flip = true;
        } else {
            R = *is_refl_relation(lhs, a, b);
            flip = false;
        }
        expr a_R_b;
        if (R == get_eq_name()) {
            a_R_b        = *get_eq_proof(a, b);
        } else if (R == get_heq_name()) {
            a_R_b        = *get_heq_proof(a, b);
        } else {
            /* TODO(Leo): the following code assumes R is homogeneous.
               We should add support arbitrary heterogenous reflexive relations. */
            expr a_eq_b  = *get_eq_proof(a, b);
            a_R_b        = lift_from_eq(m_ctx, R, a_eq_b);
        }
        expr a_R_b_eq_true = mk_eq_true_intro(m_ctx, a_R_b);
        if (flip)
            return mk_eq_symm(m_ctx, a_R_b_eq_true);
        else
            return a_R_b_eq_true;
    } else if (H == *g_refl_mark) {
        expr type  = heq_proofs ? mk_heq(m_ctx, lhs, rhs) : mk_eq(m_ctx, lhs, rhs);
        expr proof = heq_proofs ? mk_heq_refl(m_ctx, lhs) : mk_eq_refl(m_ctx, lhs);
        return mk_app(mk_constant(get_id_name(), {mk_level_zero()}), type, proof);
    } else if (is_cc_theory_proof(H)) {
        return expand_delayed_cc_proofs(*this, get_cc_theory_proof_arg(H));
    } else {
        return H;
    }
}

/*
   If as_heq is true, then build a proof for (e1 == e2).
   Otherwise, build a proof for (e1 = e2).
   The result is none if e1 and e2 are not in the same equivalence class. */
optional<expr> congruence_closure::get_eq_proof_core(expr const & e1, expr const & e2, bool as_heq) const {
    if (has_expr_metavar(e1) || has_expr_metavar(e2)) return none_expr();
    if (is_def_eq(e1, e2))
        return as_heq ? some_expr(mk_heq_refl(m_ctx, e1)) : some_expr(mk_eq_refl(m_ctx, e1));
    auto n1 = get_entry(e1);
    if (!n1) return none_expr();
    auto n2 = get_entry(e2);
    if (!n2) return none_expr();
    if (n1->m_root != n2->m_root) return none_expr();
    bool heq_proofs = has_heq_proofs(n1->m_root);
    // 1. Retrieve "path" from e1 to root
    buffer<expr> path1, Hs1;
    rb_expr_tree visited;
    expr it1 = e1;
    while (true) {
        visited.insert(it1);
        auto it1_n = get_entry(it1);
        lean_assert(it1_n);
        if (!it1_n->m_target)
            break;
        path1.push_back(*it1_n->m_target);
        Hs1.push_back(flip_proof(*it1_n->m_proof, it1_n->m_flipped, heq_proofs));
        it1 = *it1_n->m_target;
    }
    lean_assert(it1 == n1->m_root);
    // 2. The path from e2 to root must have at least one element c in visited
    // Retrieve "path" from e2 to c
    buffer<expr> path2, Hs2;
    expr it2 = e2;
    while (true) {
        if (visited.contains(it2))
            break; // found common
        auto it2_n = get_entry(it2);
        lean_assert(it2_n);
        lean_assert(it2_n->m_target);
        path2.push_back(it2);
        Hs2.push_back(flip_proof(*it2_n->m_proof, !it2_n->m_flipped, heq_proofs));
        it2 = *it2_n->m_target;
    }
    // it2 is the common element...
    // 3. Shrink path1/Hs1 until we find it2 (the common element)
    while (true) {
        if (path1.empty()) {
            lean_assert(it2 == e1);
            break;
        }
        if (path1.back() == it2) {
            // found it!
            break;
        }
        path1.pop_back();
        Hs1.pop_back();
    }

    // 4. Build transitivity proof
    optional<expr> pr;
    expr lhs = e1;
    for (unsigned i = 0; i < path1.size(); i++) {
        pr  = mk_trans(pr, mk_proof(lhs, path1[i], Hs1[i], heq_proofs), heq_proofs);
        lhs = path1[i];
    }
    unsigned i = Hs2.size();
    while (i > 0) {
        --i;
        pr  = mk_trans(pr, mk_proof(lhs, path2[i], Hs2[i], heq_proofs), heq_proofs);
        lhs = path2[i];
    }
    lean_assert(pr);
    if (heq_proofs && !as_heq)
        pr = mk_eq_of_heq(m_ctx, *pr);
    else if (!heq_proofs && as_heq)
        pr = mk_heq_of_eq(m_ctx, *pr);
    return pr;
}

optional<expr> congruence_closure::get_eq_proof(expr const & e1, expr const & e2) const {
    return get_eq_proof_core(e1, e2, false);
}

optional<expr> congruence_closure::get_heq_proof(expr const & e1, expr const & e2) const {
    return get_eq_proof_core(e1, e2, true);
}

optional<expr> congruence_closure::get_proof(expr const & e1, expr const & e2) const {
    auto n1 = get_entry(e1);
    if (!n1) return none_expr();
    if (!has_heq_proofs(n1->m_root))
        return get_eq_proof(e1, e2);
    else if (relaxed_is_def_eq(m_ctx.infer(e1), m_ctx.infer(e2)))
        return get_eq_proof(e1, e2);
    else
        return get_heq_proof(e1, e2);
}

void congruence_closure::push_subsingleton_eq(expr const & a, expr const & b) {
    /* Remark: we must use normalize here because we have use it before
       internalizing the types of 'a' and 'b'. */
    expr A = normalize(m_ctx.infer(a));
    expr B = normalize(m_ctx.infer(b));
    /* TODO(Leo): check if the following test is a performance bottleneck */
    if (relaxed_is_def_eq(A, B)) {
        /* TODO(Leo): to improve performance we can create the following proof lazily */
        expr proof     = mk_app(m_ctx, get_subsingleton_elim_name(), a, b);
        push_eq(a, b, proof);
    } else {
        expr A_eq_B    = *get_eq_proof(A, B);
        expr proof     = mk_app(m_ctx, get_subsingleton_helim_name(), A_eq_B, a, b);
        push_heq(a, b, proof);
    }
}

void congruence_closure::check_new_subsingleton_eq(expr const & old_root, expr const & new_root) {
    lean_assert(is_eqv(old_root, new_root));
    lean_assert(get_root(old_root) == new_root);
    auto it1 = m_state.m_subsingleton_reprs.find(old_root);
    if (!it1) return;
    if (auto it2 = m_state.m_subsingleton_reprs.find(new_root)) {
        push_subsingleton_eq(*it1, *it2);
    } else {
        m_state.m_subsingleton_reprs.insert(new_root, *it1);
    }
}

/* Given a new equality e1 = e2, where e1 and e2 are constructor applications.
   Implement the following implications:

   - c a_1 ... a_n = c b_1 ... b_n => a_1 = b_1, ..., a_n = b_n

   - c_1 ... = c_2 ... => false

   where c, c_1 and c_2 are constructors */
void congruence_closure::propagate_constructor_eq(expr const & e1, expr const & e2) {
    /* Remark: is_constructor_app does not check for partially applied constructor applications.
       So, we must check whether mk_constructor_eq_constructor_inconsistency_proof fails,
       and we should not assume that mk_constructor_eq_constructor_implied_eqs will succeed. */
    optional<name> c1 = is_constructor_app(env(), e1);
    optional<name> c2 = is_constructor_app(env(), e2);
    lean_assert(c1 && c2);
    if (!is_def_eq(m_ctx.infer(e1), m_ctx.infer(e2))) {
        /* The implications above only hold if the types are equal.

           TODO(Leo): if the types are different, we may still propagate by searching the equivalence
           classes of e1 and e2 for other constructors that may have compatible types. */
        return;
    }
    expr type       = mk_eq(m_ctx, e1, e2);
    expr h          = *get_eq_proof(e1, e2);
    if (*c1 == *c2) {
        buffer<std::tuple<expr, expr, expr>> implied_eqs;
        mk_constructor_eq_constructor_implied_eqs(m_ctx, e1, e2, h, implied_eqs);
        for (std::tuple<expr, expr, expr> const & t : implied_eqs) {
            expr lhs, rhs, H;
            std::tie(lhs, rhs, H) = t;
            if (is_def_eq(m_ctx.infer(lhs), m_ctx.infer(rhs)))
                push_eq(lhs, rhs, H);
            else
                push_heq(lhs, rhs, H);
        }
    } else {
        if (optional<expr> false_pr = mk_constructor_eq_constructor_inconsistency_proof(m_ctx, e1, e2, h)) {
            expr H        = mk_app(mk_constant(get_true_eq_false_of_false_name()), *false_pr);
            push_eq(mk_true(), mk_false(), H);
        }
    }
}

/* Given c a constructor application, if p is a projection application such that major premise is equal to c,
   then propagate new equality.

   Example: if p is of the form b.1, c is of the form (x, y), and b = c, we add the equality
   (x, y).1 = x */
void congruence_closure::propagate_projection_constructor(expr const & p, expr const & c) {
    lean_verify(is_constructor_app(env(), c));
    expr const & p_fn = get_app_fn(p);
    if (!is_constant(p_fn)) return;
    projection_info const * info = get_projection_info(env(), const_name(p_fn));
    if (!info) return;
    buffer<expr> p_args;
    get_app_args(p, p_args);
    if (p_args.size() <= info->m_nparams) return;
    unsigned mkidx  = info->m_nparams;
    if (!is_eqv(p_args[mkidx], c)) return;
    if (!relaxed_is_def_eq(m_ctx.infer(p_args[mkidx]), m_ctx.infer(c))) return;
    /* Create new projection application using c (e.g., (x, y).1), and internalize it.
       The internalizer will add the new equality. */
    p_args[mkidx] = c;
    expr new_p = mk_app(p_fn, p_args);
    internalize_core(new_p, none_expr(), get_generation_of(p));
}

bool congruence_closure::is_eq_true(expr const & e) const {
    return is_eqv(e, mk_true());
}

bool congruence_closure::is_eq_false(expr const & e) const {
    return is_eqv(e, mk_false());
}

// Remark: possible optimization: use delayed proof macros for get_eq_true_proof, get_eq_false_proof and get_prop_eq_proof

expr congruence_closure::get_eq_true_proof(expr const & e) const {
    lean_assert(is_eq_true(e));
    return *get_eq_proof(e, mk_true());
}

expr congruence_closure::get_eq_false_proof(expr const & e) const {
    lean_assert(is_eq_false(e));
    return *get_eq_proof(e, mk_false());
}

expr congruence_closure::get_prop_eq_proof(expr const & a, expr const & b) const {
    lean_assert(is_eqv(a, b));
    return *get_eq_proof(a, b);
}

static expr * g_iff_eq_of_eq_true_left  = nullptr;
static expr * g_iff_eq_of_eq_true_right = nullptr;
static expr * g_iff_eq_true_of_eq       = nullptr;

void congruence_closure::propagate_iff_up(expr const & e) {
    expr a, b;
    lean_verify(is_iff(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (iff a b) = b
        push_eq(e, b, mk_app(*g_iff_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (iff a b) = a
        push_eq(e, a, mk_app(*g_iff_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (iff a b) = true
        push_eq(e, mk_true(), mk_app(*g_iff_eq_true_of_eq, a, b, get_prop_eq_proof(a, b)));
    }
}

static expr * g_and_eq_of_eq_true_left   = nullptr;
static expr * g_and_eq_of_eq_true_right  = nullptr;
static expr * g_and_eq_of_eq_false_left  = nullptr;
static expr * g_and_eq_of_eq_false_right = nullptr;
static expr * g_and_eq_of_eq             = nullptr;

void congruence_closure::propagate_and_up(expr const & e) {
    expr a, b;
    lean_verify(is_and(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (and a b) = b
        push_eq(e, b, mk_app(*g_and_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (and a b) = a
        push_eq(e, a, mk_app(*g_and_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(a)) {
        // a = false -> (and a b) = false
        push_eq(e, mk_false(), mk_app(*g_and_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_false(b)) {
        // b = false -> (and a b) = false
        push_eq(e, mk_false(), mk_app(*g_and_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (and a b) = a
        push_eq(e, a, mk_app(*g_and_eq_of_eq, a, b, get_prop_eq_proof(a, b)));
    }

    // We may also add
    // a = not b -> (and a b) = false
}

static expr * g_or_eq_of_eq_true_left   = nullptr;
static expr * g_or_eq_of_eq_true_right  = nullptr;
static expr * g_or_eq_of_eq_false_left  = nullptr;
static expr * g_or_eq_of_eq_false_right = nullptr;
static expr * g_or_eq_of_eq             = nullptr;

void congruence_closure::propagate_or_up(expr const & e) {
    expr a, b;
    lean_verify(is_or(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (or a b) = true
        push_eq(e, mk_true(), mk_app(*g_or_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (or a b) = true
        push_eq(e, mk_true(), mk_app(*g_or_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(a)) {
        // a = false -> (or a b) = b
        push_eq(e, b, mk_app(*g_or_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_false(b)) {
        // b = false -> (or a b) = a
        push_eq(e, a, mk_app(*g_or_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (or a b) = a
        push_eq(e, a, mk_app(*g_or_eq_of_eq, a, b, get_prop_eq_proof(a, b)));
    }

    // We may also add
    // a = not b -> (or a b) = true
}

static expr * g_not_eq_of_eq_true   = nullptr;
static expr * g_not_eq_of_eq_false  = nullptr;
static expr * g_false_of_a_eq_not_a = nullptr;

void congruence_closure::propagate_not_up(expr const & e) {
    expr a;
    lean_verify(is_not(e, a));

    if (is_eq_true(a)) {
        // a = true  -> not a = false
        push_eq(e, mk_false(), mk_app(*g_not_eq_of_eq_true, a, get_eq_true_proof(a)));
    } else if (is_eq_false(a)) {
        // a = false -> not a = true
        push_eq(e, mk_true(), mk_app(*g_not_eq_of_eq_false, a, get_eq_false_proof(a)));
    } else if (is_eqv(a, e)) {
        expr false_pr = mk_app(*g_false_of_a_eq_not_a, a, get_prop_eq_proof(a, e));
        expr H        = mk_app(mk_constant(get_true_eq_false_of_false_name()), false_pr);
        push_eq(mk_true(), mk_false(), H);
    }
}

static expr * g_imp_eq_of_eq_true_left       = nullptr;
static expr * g_imp_eq_of_eq_false_left      = nullptr;
static expr * g_imp_eq_of_eq_true_right      = nullptr;
static expr * g_imp_eq_true_of_eq            = nullptr;
static expr * g_not_imp_eq_of_eq_false_right = nullptr;
static expr * g_imp_eq_of_eq_false_right     = nullptr;

void congruence_closure::propagate_imp_up(expr const & e) {
    lean_assert(is_arrow(e));
    expr a = binding_domain(e);
    expr b = binding_body(e);

    if (is_eq_true(a)) {
        // a = true  -> (a -> b) = b
        push_eq(e, b, mk_app(*g_imp_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_false(a)) {
        // a = false -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(b)) {
        expr arg;
        if (is_not(a, arg)) {
            if (m_state.m_config.m_em) {
                // b = false -> (not a -> b) = a
                push_eq(e, arg, mk_app(*g_not_imp_eq_of_eq_false_right, arg, b, get_eq_false_proof(b)));
            }
        } else {
            // b = false -> (a -> b) = not a
            expr not_a = mk_not(a);
            internalize_core(not_a, none_expr(), get_generation_of(e));
            push_eq(e, not_a, mk_app(*g_imp_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
        }
    } else if (is_eqv(a, b)) {
        // a = b     -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_true_of_eq, a, b, get_prop_eq_proof(a, b)));
    }
}

static name * g_if_eq_of_eq_true  = nullptr;
static name * g_if_eq_of_eq_false = nullptr;
static name * g_if_eq_of_eq       = nullptr;

void congruence_closure::propagate_ite_up(expr const & e) {
    expr A, c, d, a, b;
    lean_verify(is_ite(e, A, c, d, a, b));

    if (is_eq_true(c)) {
        // c = true  -> (ite c a b) = a
        level lvl = get_level(m_ctx, A);
        push_eq(e, a, mk_app({mk_constant(*g_if_eq_of_eq_true, {lvl}), c, d, A, a, b, get_eq_true_proof(c)}));
    } else if (is_eq_false(c)) {
        // c = false -> (ite c a b) = b
        level lvl = get_level(m_ctx, A);
        push_eq(e, b, mk_app({mk_constant(*g_if_eq_of_eq_false, {lvl}), c, d, A, a, b, get_eq_false_proof(c)}));
    } else if (is_eqv(a, b)) {
        // a = b     -> (ite c a b) = a
        level lvl = get_level(m_ctx, A);
        push_eq(e, a, mk_app({mk_constant(*g_if_eq_of_eq, {lvl}), c, d, A, a, b, get_prop_eq_proof(a, b)}));
    }
}

bool congruence_closure::may_propagate(expr const & e) {
    return
        is_iff(e) || is_and(e) || is_or(e) || is_not(e) || is_arrow(e) || is_ite(e);
}

static name * g_ne_of_eq_of_ne = nullptr;
static name * g_ne_of_ne_of_eq = nullptr;

optional<expr> congruence_closure::mk_ne_of_eq_of_ne(expr const & a, expr const & a1, expr const & a1_ne_b) {
    lean_assert(is_eqv(a, a1));
    if (a == a1)
        return some_expr(a1_ne_b);
    auto a_eq_a1 = get_eq_proof(a, a1);
    if (!a_eq_a1) return none_expr(); // failed to build proof
    return some_expr(mk_app(m_ctx, *g_ne_of_eq_of_ne, 6, *a_eq_a1, a1_ne_b));
}

optional<expr> congruence_closure::mk_ne_of_ne_of_eq(expr const & a_ne_b1, expr const & b1, expr const & b) {
    lean_assert(is_eqv(b, b1));
    if (b == b1)
        return some_expr(a_ne_b1);
    auto b1_eq_b = get_eq_proof(b1, b);
    if (!b1_eq_b) return none_expr(); // failed to build proof
    return some_expr(mk_app(m_ctx, *g_ne_of_ne_of_eq, 6, a_ne_b1, *b1_eq_b));
}

void congruence_closure::propagate_eq_up(expr const & e) {
    /* Remark: the positive case is implemented at check_eq_true
       for any reflexive relation. */
    expr a, b;
    lean_verify(is_eq(e, a, b));
    expr ra = get_root(a);
    expr rb = get_root(b);
    if (ra != rb) {
        optional<expr> ra_ne_rb;
        if (is_interpreted_value(ra) && is_interpreted_value(rb)) {
            ra_ne_rb = mk_val_ne_proof(m_ctx, ra, rb);
        } else {
            if (optional<name> c1 = is_constructor_app(env(), ra))
            if (optional<name> c2 = is_constructor_app(env(), rb))
            if (c1 && c2 && *c1 != *c2)
                ra_ne_rb = mk_constructor_ne_constructor_proof(m_ctx, ra, rb);
        }
        if (ra_ne_rb)
        if (auto a_ne_rb = mk_ne_of_eq_of_ne(a, ra, *ra_ne_rb))
        if (auto a_ne_b = mk_ne_of_ne_of_eq(*a_ne_rb, rb, b))
            push_eq(e, mk_false(), mk_eq_false_intro(m_ctx, *a_ne_b));
    }
}

void congruence_closure::propagate_up(expr const & e) {
    if (m_state.m_inconsistent) return;
    if (is_iff(e)) {
        propagate_iff_up(e);
    } else if (is_and(e)) {
        propagate_and_up(e);
    } else if (is_or(e)) {
        propagate_or_up(e);
    } else if (is_not(e)) {
        propagate_not_up(e);
    } else if (is_arrow(e)) {
        propagate_imp_up(e);
    } else if (is_ite(e)) {
        propagate_ite_up(e);
    } else if (is_eq(e)) {
        propagate_eq_up(e);
    }
}

static expr * g_eq_true_of_and_eq_true_left  = nullptr;
static expr * g_eq_true_of_and_eq_true_right = nullptr;

void congruence_closure::propagate_and_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a, b;
        lean_verify(is_and(e, a, b));
        expr h = get_eq_true_proof(e);
        push_eq(a, mk_true(), mk_app(*g_eq_true_of_and_eq_true_left, a, b, h));
        push_eq(b, mk_true(), mk_app(*g_eq_true_of_and_eq_true_right, a, b, h));
    }
}

static expr * g_eq_false_of_or_eq_false_left  = nullptr;
static expr * g_eq_false_of_or_eq_false_right = nullptr;

void congruence_closure::propagate_or_down(expr const & e) {
    if (is_eq_false(e)) {
        expr a, b;
        lean_verify(is_or(e, a, b));
        expr h = get_eq_false_proof(e);
        push_eq(a, mk_false(), mk_app(*g_eq_false_of_or_eq_false_left, a, b, h));
        push_eq(b, mk_false(), mk_app(*g_eq_false_of_or_eq_false_right, a, b, h));
    }
}

static expr * g_eq_false_of_not_eq_true = nullptr;
static expr * g_eq_true_of_not_eq_false = nullptr;

void congruence_closure::propagate_not_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a;
        lean_verify(is_not(e, a));
        push_eq(a, mk_false(), mk_app(*g_eq_false_of_not_eq_true, a, get_eq_true_proof(e)));
    } else if (m_state.m_config.m_em && is_eq_false(e)) {
        expr a;
        lean_verify(is_not(e, a));
        push_eq(a, mk_true(), mk_app(*g_eq_true_of_not_eq_false, a, get_eq_false_proof(e)));
    }
}

void congruence_closure::propagate_eq_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a, b;
        if (is_eq(e, a, b) || is_iff(e, a, b)) {
            push_eq(a, b, mk_of_eq_true(m_ctx, get_eq_true_proof(e)));
        } else {
            lean_unreachable();
        }
    }
}

/** Given (h_not_ex : not ex) where ex is of the form (exists x, p x),
    return a (forall x, not p x) and a proof for it.

    This function handles nested existentials. */
expr_pair congruence_closure::to_forall_not(expr const & ex, expr const & h_not_ex) {
    lean_assert(is_exists(ex));
    expr A, p;
    lean_verify(is_exists(ex, A, p));
    type_context_old::tmp_locals locals(m_ctx);
    level lvl         = get_level(m_ctx, A);
    expr x            = locals.push_local("_x", A);
    expr px           = head_beta_reduce(mk_app(p, x));
    expr not_px       = mk_not(px);
    expr h_all_not_px = mk_app({mk_constant(get_forall_not_of_not_exists_name(), {lvl}), A, p, h_not_ex});
    if (is_exists(px)) {
        expr h_not_px = locals.push_local("_h", not_px);
        auto p               = to_forall_not(px, h_not_px);
        expr qx              = p.first;
        expr all_qx          = m_ctx.mk_pi(x, qx);
        expr h_qx            = p.second;
        expr h_not_px_imp_qx = m_ctx.mk_lambda(h_not_px, h_qx);
        expr h_all_qx        = m_ctx.mk_lambda({x}, mk_app(h_not_px_imp_qx, mk_app(h_all_not_px, x)));
        return mk_pair(all_qx, h_all_qx);
    } else {
        expr all_not_px      = m_ctx.mk_pi(x, not_px);
        return mk_pair(all_not_px, h_all_not_px);
    }
}

void congruence_closure::propagate_exists_down(expr const & e) {
    if (is_eq_false(e)) {
        expr h_not_e = mk_not_of_eq_false(m_ctx, get_eq_false_proof(e));
        expr all, h_all;
        std::tie(all, h_all) = to_forall_not(e, h_not_e);
        internalize_core(all, none_expr(), get_generation_of(e));
        push_eq(all, mk_true(), mk_eq_true_intro(m_ctx, h_all));
    }
}

void congruence_closure::propagate_down(expr const & e) {
    if (is_and(e)) {
        propagate_and_down(e);
    } else if (is_or(e)) {
        propagate_or_down(e);
    } else if (is_not(e)) {
        propagate_not_down(e);
    } else if (is_eq(e) || is_iff(e)) {
        propagate_eq_down(e);
    } else if (is_exists(e)) {
        propagate_exists_down(e);
    }
}

void congruence_closure::propagate_value_inconsistency(expr const & e1, expr const & e2) {
    lean_assert(is_interpreted_value(e1));
    lean_assert(is_interpreted_value(e2));
    expr ne_proof      = *mk_val_ne_proof(m_ctx, e1, e2);
    expr eq_proof      = *get_eq_proof(e1, e2);
    expr true_eq_false = mk_eq(m_ctx, mk_true(), mk_false());
    expr H             = mk_absurd(m_ctx, eq_proof, ne_proof, true_eq_false);
    push_eq(mk_true(), mk_false(), H);
}

static bool is_true_or_false(expr const & e) {
    return is_constant(e, get_true_name()) || is_constant(e, get_false_name());
}

void congruence_closure::get_eqc_lambdas(expr const & e, buffer<expr> & r) {
    lean_assert(get_root(e) == e);
    if (!get_entry(e)->m_has_lambdas) return;
    auto it = e;
    do {
        if (is_lambda(it))
            r.push_back(it);
        auto it_n = get_entry(it);
        it = it_n->m_next;
    } while (it != e);
}

void congruence_closure::propagate_beta(expr const & fn, buffer<expr> const & rev_args,
                                        buffer<expr> const & lambdas, buffer<expr> & new_lambda_apps) {
    for (expr const & lambda : lambdas) {
        lean_assert(is_lambda(lambda));
        if (fn != lambda && relaxed_is_def_eq(m_ctx.infer(fn), m_ctx.infer(lambda))) {
            expr new_app = mk_rev_app(lambda, rev_args);
            new_lambda_apps.push_back(new_app);
        }
    }
}

/* Traverse the root's equivalence class, and collect the function's equivalence class roots. */
void congruence_closure::collect_fn_roots(expr const & root, buffer<expr> & fn_roots) {
    lean_assert(get_root(root) == root);
    rb_expr_tree visited;
    auto it = root;
    do {
        expr fn_root = get_root(get_app_fn(it));
        if (!visited.contains(fn_root)) {
            visited.insert(fn_root);
            fn_roots.push_back(fn_root);
        }
        auto it_n = get_entry(it);
        it = it_n->m_next;
    } while (it != root);
}

/* For each fn_root in fn_roots traverse its parents, and look for a parent prefix that is
   in the same equivalence class of the given lambdas.

   \remark All expressions in lambdas are in the same equivalence class */
void congruence_closure::propagate_beta_to_eqc(buffer<expr> const & fn_roots, buffer<expr> const & lambdas,
                                               buffer<expr> & new_lambda_apps) {
    if (lambdas.empty()) return;
    expr const & lambda_root = get_root(lambdas.back());
    lean_assert(std::all_of(lambdas.begin(), lambdas.end(), [&](expr const & l) {
                return is_lambda(l) && get_root(l) == lambda_root;
            }));
    for (expr const & fn_root : fn_roots) {
        if (auto ps = m_state.m_parents.find(fn_root)) {
            ps->for_each([&](parent_occ const & p_occ) {
                    expr const & p = p_occ.m_expr;
                    /* Look for a prefix of p which is in the same equivalence class of lambda_root */
                    buffer<expr> rev_args;
                    expr it2 = p;
                    while (is_app(it2)) {
                        expr const & fn = app_fn(it2);
                        rev_args.push_back(app_arg(it2));
                        if (get_root(fn) == lambda_root) {
                            /* found it */
                            propagate_beta(fn, rev_args, lambdas, new_lambda_apps);
                            break;
                        }
                        it2 = app_fn(it2);
                    }
                });
        }
    }
}

void congruence_closure::add_eqv_step(expr e1, expr e2, expr const & H, bool heq_proof) {
    auto n1 = get_entry(e1);
    auto n2 = get_entry(e2);
    if (!n1 || !n2)
        return; /* e1 and e2 have not been internalized */
    if (n1->m_root == n2->m_root)
        return; /* they are already in the same equivalence class. */
    auto r1 = get_entry(n1->m_root);
    auto r2 = get_entry(n2->m_root);
    lean_assert(r1 && r2);
    bool flipped = false;

    /* We want r2 to be the root of the combined class. */

    /*
     We swap (e1,n1,r1) with (e2,n2,r2) when
     1- r1->m_interpreted && !r2->m_interpreted.
        Reason: to decide when to propagate we check whether the root of the equivalence class
        is true/false. So, this condition is to make sure if true/false is in an equivalence class,
        then one of them is the root. If both are, it doesn't matter, since the state is inconsistent
        anyway.
     2- r1->m_constructor && !r2->m_interpreted && !r2->m_constructor
        Reason: we want constructors to be the representative of their equivalence classes.
     3- r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor
        Reason: performance.
    */
    if ((r1->m_interpreted && !r2->m_interpreted) ||
        (r1->m_constructor && !r2->m_interpreted && !r2->m_constructor) ||
        (r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor)) {
        std::swap(e1, e2);
        std::swap(n1, n2);
        std::swap(r1, r2);
        // Remark: we don't apply symmetry eagerly. So, we don't adjust H.
        flipped = true;
    }

    bool value_inconsistency = false;
    if (r1->m_interpreted && r2->m_interpreted) {
        if (is_true(n1->m_root) || is_true(n2->m_root)) {
            m_state.m_inconsistent = true;
        } else if (is_num(n1->m_root) && is_num(n2->m_root)) {
            /* Little hack to cope with the fact that we don't have a canonical representation
               for nat numerals. For example: is_num returns true for
               both (nat.succ nat.zero) and (@one nat nat.has_one). */
            value_inconsistency = to_num(n1->m_root) != to_num(n2->m_root);
        } else {
            value_inconsistency = true;
        }
    }

    bool constructor_eq = r1->m_constructor && r2->m_constructor;
    expr e1_root   = n1->m_root;
    expr e2_root   = n2->m_root;
    entry new_n1   = *n1;
    lean_trace(name({"debug", "cc"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               tout() << "merging:\n" << e1 << " ==> " << e1_root << "\nwith\n" << e2_root << " <== " << e2 << "\n";);

    /*
     Following target/proof we have
     e1 -> ... -> r1
     e2 -> ... -> r2
     We want
     r1 -> ... -> e1 -> e2 -> ... -> r2
    */
    invert_trans(e1);
    new_n1.m_target  = e2;
    new_n1.m_proof   = H;
    new_n1.m_flipped = flipped;
    m_state.m_entries.insert(e1, new_n1);

    buffer<expr> parents_to_propagate;
    /* The hash code for the parents is going to change */
    remove_parents(e1_root, parents_to_propagate);

    buffer<expr> lambdas1, lambdas2;
    get_eqc_lambdas(e1_root, lambdas1);
    get_eqc_lambdas(e2_root, lambdas2);
    buffer<expr> fn_roots1, fn_roots2;
    if (!lambdas1.empty()) collect_fn_roots(e2_root, fn_roots2);
    if (!lambdas2.empty()) collect_fn_roots(e1_root, fn_roots1);

    /* force all m_root fields in e1 equivalence class to point to e2_root */
    bool propagate = is_true_or_false(e2_root);
    buffer<expr> to_propagate;
    expr it = e1;
    do {
        auto it_n = get_entry(it);
        if (propagate)
            to_propagate.push_back(it);
        lean_assert(it_n);
        entry new_it_n   = *it_n;
        new_it_n.m_root = e2_root;
        m_state.m_entries.insert(it, new_it_n);
        it = new_it_n.m_next;
    } while (it != e1);

    reinsert_parents(e1_root);

    // update next of e1_root and e2_root, ac representative, and size of e2_root
    r1 = get_entry(e1_root);
    r2 = get_entry(e2_root);
    lean_assert(r1 && r2);
    lean_assert(r1->m_root == e2_root);

    entry new_r1          = *r1;
    entry new_r2          = *r2;
    new_r1.m_next         = r2->m_next;
    new_r2.m_next         = r1->m_next;
    new_r2.m_size        += r1->m_size;
    new_r2.m_has_lambdas |= r1->m_has_lambdas;
    optional<expr> ac_var1 = r1->m_ac_var;
    optional<expr> ac_var2 = r2->m_ac_var;
    if (!ac_var2)
        new_r2.m_ac_var    = ac_var1;
    if (heq_proof)
        new_r2.m_heq_proofs = true;
    m_state.m_entries.insert(e1_root, new_r1);
    m_state.m_entries.insert(e2_root, new_r2);
    lean_assert(check_invariant());

    buffer<expr> lambda_apps_to_internalize;
    propagate_beta_to_eqc(fn_roots2, lambdas1, lambda_apps_to_internalize);
    propagate_beta_to_eqc(fn_roots1, lambdas2, lambda_apps_to_internalize);

    // copy e1_root parents to e2_root
    auto ps1 = m_state.m_parents.find(e1_root);
    if (ps1) {
        parent_occ_set ps2;
        if (auto it = m_state.m_parents.find(e2_root))
            ps2 = *it;
        ps1->for_each([&](parent_occ const & p) {
                if (!is_app(p.m_expr) || is_congr_root(p.m_expr)) {
                    if (!constructor_eq && r2->m_constructor)  {
                        propagate_projection_constructor(p.m_expr, e2_root);
                    }
                    ps2.insert(p);
                }
            });
        m_state.m_parents.erase(e1_root);
        m_state.m_parents.insert(e2_root, ps2);
    }

    if (!m_state.m_inconsistent && ac_var1 && ac_var2)
        m_ac.add_eq(*ac_var1, *ac_var2);

    if (!m_state.m_inconsistent && constructor_eq)
        propagate_constructor_eq(e1_root, e2_root);

    if (!m_state.m_inconsistent && value_inconsistency)
        propagate_value_inconsistency(e1_root, e2_root);

    if (!m_state.m_inconsistent) {
        update_mt(e2_root);
        check_new_subsingleton_eq(e1_root, e2_root);
    }

    if (!m_state.m_inconsistent) {
        for (expr const & p : parents_to_propagate)
            propagate_up(p);
    }

    if (!m_state.m_inconsistent && !to_propagate.empty()) {
        for (expr const & e : to_propagate)
            propagate_down(e);
        if (m_phandler)
            m_phandler->propagated(to_propagate);
    }

    if (!m_state.m_inconsistent) {
        for (expr const & e : lambda_apps_to_internalize) {
            internalize_core(e, none_expr(), get_generation_of(e));
        }
    }

    lean_trace(name({"cc", "merge"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               tout() << e1_root << " = " << e2_root << "\n";);
    lean_trace(name({"debug", "cc"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << "merged: " << e1_root << " = " << e2_root << "\n";
               out << m_state.pp_eqcs(fmt) << "\n";
               if (is_trace_class_enabled(name{"debug", "cc", "parent_occs"}))
                   out << m_state.pp_parent_occs(fmt) << "\n";
               out << "--------\n";);
}

void congruence_closure::process_todo() {
    while (!m_todo.empty()) {
        if (m_state.m_inconsistent) {
            m_todo.clear();
            return;
        }
        expr lhs, rhs, H; bool heq_proof;
        std::tie(lhs, rhs, H, heq_proof) = m_todo.back();
        m_todo.pop_back();
        add_eqv_step(lhs, rhs, H, heq_proof);
    }
}

void congruence_closure::add_eqv_core(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof) {
    push_todo(lhs, rhs, H, heq_proof);
    process_todo();
}

void congruence_closure::add(expr const & type, expr const & proof, unsigned gen) {
    if (m_state.m_inconsistent) return;
    m_todo.clear();
    expr p      = type;
    bool is_neg = is_not_or_ne(type, p);
    expr lhs, rhs;
    if (is_eq(type, lhs, rhs) || is_heq(type, lhs, rhs)) {
        if (is_neg) {
            bool heq_proof    = false;
            internalize_core(p, none_expr(), gen);
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, proof), heq_proof);
        } else {
            bool heq_proof    = is_heq(type);
            internalize_core(lhs, none_expr(), gen);
            internalize_core(rhs, none_expr(), gen);
            add_eqv_core(lhs, rhs, proof, heq_proof);
        }
    } else if (is_iff(type, lhs, rhs)) {
        bool heq_proof    = false;
        if (is_neg) {
            expr neq_proof = mk_neq_of_not_iff(m_ctx, proof);
            internalize_core(p, none_expr(), gen);
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, neq_proof), heq_proof);
        } else {
            internalize_core(lhs, none_expr(), gen);
            internalize_core(rhs, none_expr(), gen);
            add_eqv_core(lhs, rhs, mk_propext(lhs, rhs, proof), heq_proof);
        }
    } else if (is_neg || m_ctx.is_prop(p)) {
        bool heq_proof    = false;
        internalize_core(p, none_expr(), gen);
        if (is_neg) {
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, proof), heq_proof);
        } else {
            add_eqv_core(p, mk_true(), mk_eq_true_intro(m_ctx, proof), heq_proof);
        }
    }
}

bool congruence_closure::is_eqv(expr const & e1, expr const & e2) const {
    auto n1 = get_entry(e1);
    if (!n1) return false;
    auto n2 = get_entry(e2);
    if (!n2) return false;
    /* Remark: this method assumes that is_eqv is invoked with type correct parameters.
       An eq class may contain equality and heterogeneous equality proofs is enabled.
       When this happens, the answer is correct only if e1 and e2 have the same type. */
    return n1->m_root == n2->m_root;
}

bool congruence_closure::is_not_eqv(expr const & e1, expr const & e2) const {
    try {
        expr tmp = mk_eq(m_ctx, e1, e2);
        if (is_eqv(tmp, mk_false()))
            return true;
        tmp = mk_heq(m_ctx, e1, e2);
        return is_eqv(tmp, mk_false());
    } catch (app_builder_exception &) {
        return false;
    }
}

bool congruence_closure::proved(expr const & e) const {
    return is_eqv(e, mk_true());
}

void congruence_closure::internalize(expr const & e, unsigned gen) {
    internalize_core(e, none_expr(), gen);
    process_todo();
}

optional<expr> congruence_closure::get_inconsistency_proof() const {
    lean_assert(!m_state.m_froze_partitions);
    try {
        if (auto p = get_eq_proof(mk_true(), mk_false())) {
            return some_expr(mk_false_of_true_eq_false(m_ctx, *p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::state::check_eqc(expr const & e) const {
    expr root     = get_root(e);
    unsigned size = 0;
    expr it       = e;
    do {
        auto it_n = m_entries.find(it);
        lean_assert(it_n);
        lean_assert(it_n->m_root == root);
        auto it2  = it;
        // following m_target fields should lead to root
        while (true) {
            auto it2_n = m_entries.find(it2);
            if (!it2_n->m_target)
                break;
            it2 = *it2_n->m_target;
        }
        lean_assert(it2 == root);
        it = it_n->m_next;
        size++;
    } while (it != e);
    lean_assert(m_entries.find(root)->m_size == size);
    return true;
}

bool congruence_closure::state::check_invariant() const {
    m_entries.for_each([&](expr const & k, entry const & n) {
            if (k == n.m_root) {
                lean_assert(check_eqc(k));
            }
        });
    return true;
}

format congruence_closure::state::pp_eqc(formatter const & fmt, expr const & e) const {
    format r;
    bool first = true;
    expr it = e;
    do {
        auto it_n = m_entries.find(it);
        if (first) first = false; else r += comma() + line();
        format fmt_it = fmt(it);
        if (is_pi(it) || is_lambda(it) || is_let(it))
            fmt_it = paren(fmt_it);
        r += fmt_it;
        it = it_n->m_next;
    } while (it != e);
    return bracket("{", group(r), "}");
}

bool congruence_closure::state::in_singleton_eqc(expr const & e) const {
    if (auto it = m_entries.find(e))
        return it->m_next == e;
    return  true;
}

format congruence_closure::state::pp_eqcs(formatter const & fmt, bool nonsingleton_only) const {
    buffer<expr> roots;
    get_roots(roots, nonsingleton_only);
    format r;
    bool first = true;
    for (expr const & root : roots) {
        if (first) first = false; else r += comma() + line();
        r += pp_eqc(fmt, root);
    }
    return bracket("{", group(r), "}");
}

format congruence_closure::state::pp_parent_occs(formatter const & fmt, expr const & e) const {
    format r = fmt(e) + line() + format(":=") + line();
    format ps;
    if (parent_occ_set const * poccs = m_parents.find(e)) {
        bool first = true;
        poccs->for_each([&](parent_occ const & o) {
                if (first) first = false; else ps += comma() + line();
                ps += fmt(o.m_expr);
            });
    }
    return group(r + bracket("{", group(ps), "}"));
}

format congruence_closure::state::pp_parent_occs(formatter const & fmt) const {
    format r;
    bool first = true;
    m_parents.for_each([&](expr const & k, parent_occ_set const &) {
            if (first) first = false; else r += comma() + line();
            r += pp_parent_occs(fmt, k);
        });
    return group(bracket("{", group(r), "}"));
}

void initialize_congruence_closure() {
    register_trace_class("cc");
    register_trace_class({"cc", "failure"});
    register_trace_class({"cc", "merge"});
    register_trace_class({"debug", "cc"});
    register_trace_class({"debug", "cc", "parent_occs"});

    name prefix     = name::mk_internal_unique_name();
    g_congr_mark    = new expr(mk_constant(name(prefix, "[congruence]")));
    g_eq_true_mark  = new expr(mk_constant(name(prefix, "[iff-true]")));
    g_refl_mark     = new expr(mk_constant(name(prefix, "[refl]")));

    g_iff_eq_of_eq_true_left  = new expr(mk_constant("iff_eq_of_eq_true_left"));
    g_iff_eq_of_eq_true_right = new expr(mk_constant("iff_eq_of_eq_true_right"));
    g_iff_eq_true_of_eq       = new expr(mk_constant("iff_eq_true_of_eq"));

    g_and_eq_of_eq_true_left   = new expr(mk_constant("and_eq_of_eq_true_left"));
    g_and_eq_of_eq_true_right  = new expr(mk_constant("and_eq_of_eq_true_right"));
    g_and_eq_of_eq_false_left  = new expr(mk_constant("and_eq_of_eq_false_left"));
    g_and_eq_of_eq_false_right = new expr(mk_constant("and_eq_of_eq_false_right"));
    g_and_eq_of_eq             = new expr(mk_constant("and_eq_of_eq"));

    g_or_eq_of_eq_true_left   = new expr(mk_constant("or_eq_of_eq_true_left"));
    g_or_eq_of_eq_true_right  = new expr(mk_constant("or_eq_of_eq_true_right"));
    g_or_eq_of_eq_false_left  = new expr(mk_constant("or_eq_of_eq_false_left"));
    g_or_eq_of_eq_false_right = new expr(mk_constant("or_eq_of_eq_false_right"));
    g_or_eq_of_eq             = new expr(mk_constant("or_eq_of_eq"));

    g_not_eq_of_eq_true       = new expr(mk_constant("not_eq_of_eq_true"));
    g_not_eq_of_eq_false      = new expr(mk_constant("not_eq_of_eq_false"));
    g_false_of_a_eq_not_a     = new expr(mk_constant("false_of_a_eq_not_a"));

    g_imp_eq_of_eq_true_left  = new expr(mk_constant("imp_eq_of_eq_true_left"));
    g_imp_eq_of_eq_false_left = new expr(mk_constant("imp_eq_of_eq_false_left"));
    g_imp_eq_of_eq_true_right = new expr(mk_constant("imp_eq_of_eq_true_right"));
    g_imp_eq_true_of_eq       = new expr(mk_constant("imp_eq_true_of_eq"));

    g_not_imp_eq_of_eq_false_right = new expr(mk_constant("not_imp_eq_of_eq_false_right"));
    g_imp_eq_of_eq_false_right     = new expr(mk_constant("imp_eq_of_eq_false_right"));

    g_if_eq_of_eq_true  = new name("if_eq_of_eq_true");
    g_if_eq_of_eq_false = new name("if_eq_of_eq_false");
    g_if_eq_of_eq       = new name("if_eq_of_eq");

    g_eq_true_of_and_eq_true_left  = new expr(mk_constant("eq_true_of_and_eq_true_left"));
    g_eq_true_of_and_eq_true_right = new expr(mk_constant("eq_true_of_and_eq_true_right"));

    g_eq_false_of_or_eq_false_left  = new expr(mk_constant("eq_false_of_or_eq_false_left"));
    g_eq_false_of_or_eq_false_right = new expr(mk_constant("eq_false_of_or_eq_false_right"));

    g_eq_false_of_not_eq_true = new expr(mk_constant("eq_false_of_not_eq_true"));
    g_eq_true_of_not_eq_false = new expr(mk_constant("eq_true_of_not_eq_false"));

    g_ne_of_eq_of_ne   = new name("ne_of_eq_of_ne");
    g_ne_of_ne_of_eq   = new name("ne_of_ne_of_eq");
}

void finalize_congruence_closure() {
    delete g_congr_mark;
    delete g_eq_true_mark;
    delete g_refl_mark;

    delete g_iff_eq_of_eq_true_left;
    delete g_iff_eq_of_eq_true_right;
    delete g_iff_eq_true_of_eq;

    delete g_and_eq_of_eq_true_left;
    delete g_and_eq_of_eq_true_right;
    delete g_and_eq_of_eq_false_left;
    delete g_and_eq_of_eq_false_right;
    delete g_and_eq_of_eq;

    delete g_or_eq_of_eq_true_left;
    delete g_or_eq_of_eq_true_right;
    delete g_or_eq_of_eq_false_left;
    delete g_or_eq_of_eq_false_right;
    delete g_or_eq_of_eq;

    delete g_not_eq_of_eq_true;
    delete g_not_eq_of_eq_false;
    delete g_false_of_a_eq_not_a;

    delete g_imp_eq_of_eq_true_left;
    delete g_imp_eq_of_eq_false_left;
    delete g_imp_eq_of_eq_true_right;
    delete g_imp_eq_true_of_eq;

    delete g_not_imp_eq_of_eq_false_right;
    delete g_imp_eq_of_eq_false_right;

    delete g_if_eq_of_eq_true;
    delete g_if_eq_of_eq_false;
    delete g_if_eq_of_eq;

    delete g_eq_true_of_and_eq_true_left;
    delete g_eq_true_of_and_eq_true_right;

    delete g_eq_false_of_or_eq_false_left;
    delete g_eq_false_of_or_eq_false_right;

    delete g_eq_false_of_not_eq_true;
    delete g_eq_true_of_not_eq_false;

    delete g_ne_of_eq_of_ne;
    delete g_ne_of_ne_of_eq;
}
}
```

src/library/tactic/smt/congruence_tactics.h:
```c++
namespace lean {
bool is_cc_state(vm_obj const & o);
congruence_closure::state const & to_cc_state(vm_obj const & o);
vm_obj to_obj(congruence_closure::state const & s);

tactic_state update_defeq_canonizer_state(tactic_state const & s, congruence_closure const & cc);

void initialize_congruence_tactics();
void finalize_congruence_tactics();
}
```

src/library/tactic/smt/congruence_tactics.cpp:
```c++
namespace lean {
struct vm_cc_state : public vm_external {
    congruence_closure::state m_val;
    vm_cc_state(congruence_closure::state const & v):m_val(v) {}
    virtual ~vm_cc_state() {}
    virtual void dealloc() override {
        this->~vm_cc_state(); get_vm_allocator().deallocate(sizeof(vm_cc_state), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_cc_state(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(m_val); }
    virtual unsigned int hash() { return 0; }
};

bool is_cc_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_cc_state*>(to_external(o));
}

congruence_closure::state const & to_cc_state(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_cc_state*>(to_external(o)));
    return static_cast<vm_cc_state*>(to_external(o))->m_val;
}

vm_obj to_obj(congruence_closure::state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(s));
}

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
(em               : bool)
*/
pair<name_set, congruence_closure::config> to_ho_fns_cc_config(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    c.m_ignore_instances = to_bool(cfield(cfg, 0));
    c.m_ac               = to_bool(cfield(cfg, 1));
    if (is_none(cfield(cfg, 2))) {
        c.m_all_ho       = true;
    } else {
        c.m_all_ho       = false;
        ho_fns           = to_name_set(to_list_name(get_some_value(cfield(cfg, 2))));
    }
    c.m_em               = to_bool(cfield(cfg, 3));
    return mk_pair(ho_fns, c);
}

static congruence_closure::state mk_core(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    std::tie(ho_fns, c) = to_ho_fns_cc_config(cfg);
    return congruence_closure::state(ho_fns, c);
}

vm_obj cc_state_mk_core(vm_obj const & cfg) {
    return to_obj(mk_core(cfg));
}

vm_obj cc_state_mk_using_hs_core(vm_obj const & cfg, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        local_context lctx          = g->get_context();
        type_context_old ctx            = mk_type_context_for(s);
        defeq_can_state dcs         = s.dcs();
        congruence_closure::state r = mk_core(cfg);
        congruence_closure cc(ctx, r, dcs);
        lctx.for_each([&](local_decl const & d) {
                if (ctx.is_prop(d.get_type())) {
                    cc.add(d.get_type(), d.mk_ref(), 0);
                }
            });
        tactic_state new_s = set_dcs(s, dcs);
        return tactic::mk_success(to_obj(r), new_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj cc_state_pp_core(vm_obj const & ccs, vm_obj const & nonsingleton, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqcs(fmt, to_bool(nonsingleton));
    return tactic::mk_success(to_obj(r), s);
}

vm_obj cc_state_pp_eqc(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqc(fmt, to_expr(e));
    return tactic::mk_success(to_obj(r), s);
}

vm_obj cc_state_next(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_next(to_expr(e)));
}

vm_obj cc_state_root(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_root(to_expr(e)));
}

vm_obj cc_state_is_cg_root(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_bool(to_cc_state(ccs).is_congr_root(to_expr(e)));
}

vm_obj cc_state_roots_core(vm_obj const & ccs, vm_obj const & nonsingleton) {
    buffer<expr> roots;
    to_cc_state(ccs).get_roots(roots, to_bool(nonsingleton));
    return to_obj(roots);
}

vm_obj cc_state_inconsistent(vm_obj const & ccs) {
    return mk_vm_bool(to_cc_state(ccs).inconsistent());
}

vm_obj cc_state_mt(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_nat(to_cc_state(ccs).get_mt(to_expr(e)));
}

vm_obj cc_state_gmt(vm_obj const & ccs) {
    return mk_vm_nat(to_cc_state(ccs).get_gmt());
}

vm_obj cc_state_inc_gmt(vm_obj const & ccs) {
    congruence_closure::state s = to_cc_state(ccs);
    s.inc_gmt();
    return to_obj(s);
}

#define cc_state_proc(CODE)                                     \
    tactic_state const & s   = tactic::to_state(_s);             \
    try {                                                       \
        type_context_old ctx            = mk_type_context_for(s);   \
        congruence_closure::state S = to_cc_state(ccs);         \
        defeq_can_state dcs         = s.dcs();                  \
        congruence_closure cc(ctx, S, dcs);                     \
        CODE                                                    \
    } catch (exception & ex) {                                  \
        return tactic::mk_exception(ex, s);                      \
    }

#define cc_state_updt_proc(CODE) cc_state_proc({ CODE; return tactic::mk_success(to_obj(S), set_dcs(s, dcs)); })

vm_obj cc_state_add(vm_obj const & ccs, vm_obj const & H, vm_obj const & _s) {
    cc_state_updt_proc({
            expr type                   = ctx.infer(to_expr(H));
            if (!ctx.is_prop(type))
                return tactic::mk_exception("cc_state.add failed, given expression is not a proof term", s);
            cc.add(type, to_expr(H), 0);
    });
}

vm_obj cc_state_internalize(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_updt_proc({
            cc.internalize(to_expr(e), 0);
        });
}

vm_obj cc_state_is_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_is_not_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_not_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_eqv_proof(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_proof(to_expr(e1), to_expr(e2))) {
                return tactic::mk_success(to_obj(*r), s);
            } else {
                return tactic::mk_exception("cc_state.eqv_proof failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_true())) {
                return tactic::mk_success(to_obj(mk_of_eq_true(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_proof_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_refutation_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_false())) {
                return tactic::mk_success(to_obj(mk_not_of_eq_false(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_refutation_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for_false(vm_obj const & ccs, vm_obj const & _s) {
    cc_state_proc({
            if (auto pr = cc.get_inconsistency_proof()) {
                return tactic::mk_success(to_obj(*pr), s);
            } else {
                return tactic::mk_exception("cc_state.false_proof failed, state is not inconsistent", s);
            }
        });
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_core"}),              cc_state_mk_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs_core"}),     cc_state_mk_using_hs_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_core"}),              cc_state_pp_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_eqc"}),               cc_state_pp_eqc);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "root"}),                 cc_state_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "mt"}),                   cc_state_mt);
    DECLARE_VM_BUILTIN(name({"cc_state", "gmt"}),                  cc_state_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "inc_gmt"}),              cc_state_inc_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_cg_root"}),           cc_state_is_cg_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "roots_core"}),           cc_state_roots_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "internalize"}),          cc_state_internalize);
    DECLARE_VM_BUILTIN(name({"cc_state", "add"}),                  cc_state_add);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_eqv"}),               cc_state_is_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_not_eqv"}),           cc_state_is_not_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "inconsistent"}),         cc_state_inconsistent);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for_false"}),      cc_state_proof_for_false);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),            cc_state_eqv_proof);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for"}),            cc_state_proof_for);
    DECLARE_VM_BUILTIN(name({"cc_state", "refutation_for"}),       cc_state_refutation_for);
}

void finalize_congruence_tactics() {
}
}
```
-/

/-- Equivalence class data associated with an expression `e` -/
structure Entry where
  /-- next element in the equivalence class. -/
  next : Expr
  /-- root (aka canonical) representative of the equivalence class. -/
  root : Expr
  /-- root of the congruence class, it is meaningless if `e` is not an application. -/
  cgRoot : Expr
  /-- When `e` was added to this equivalence class because of an equality `(H : e = tgt)`, then
      we store `tgt` at `target`, and `H` at `proof`. Both fields are none if `e == root` -/
  target : Option Expr := none
  /-- When `e` was added to this equivalence class because of an equality `(H : e = tgt)`, then
      we store `tgt` at `target`, and `H` at `proof`. Both fields are none if `e == root` -/
  proof : Option Expr := none
  /-- proof has been flipped -/
  flipped : Bool
  /-- `true` if the node should be viewed as an abstract value -/
  interpreted : Bool
  /-- `true` if head symbol is a constructor -/
  constructor : Bool
  /-- `true` if equivalence class contains lambda expressions -/
  hasLambdas : Bool
  /-- `heqProofs == true` iff some proofs in the equivalence class are based on heterogeneous
      equality. We represent equality and heterogeneous equality in a single equivalence class. -/
  heqProofs : Bool
  /-- If `fo == true`, then the expression associated with this entry is an application, and we are
      using first-order approximation to encode it. That is, we ignore its partial applications. -/
  fo : Bool
  /-- number of elements in the equivalence class, it is meaningless if `e != root` -/
  size : Nat
  /-- The field `mt` is used to implement the mod-time optimization introduce by the Simplify
      theorem prover. The basic idea is to introduce a counter gmt that records the number of
      heuristic instantiation that have occurred in the current branch. It is incremented after each
      round of heuristic instantiation. The field `mt` records the last time any proper descendant
      of of thie entry was involved in a merge. -/
  mt : Nat
  generation : Nat

abbrev Entries := RBExprMap Entry

structure ParentOcc where
  expr : Expr
  /-- If `symmTable` is true, then we should use the `symmCongruences`, otherwise `congruences`.
      Remark: this information is redundant, it can be inferred from `expr`. We use store it for
      performance reasons. -/
  symmTable : Bool

abbrev ParentOccSet := Std.RBSet ParentOcc (byKey ParentOcc.expr Expr.quickCmp)

abbrev Parents := RBExprMap ParentOccSet

abbrev Congruences := UInt64Map (List Expr)

abbrev SymmCongruences := UInt64Map (List (Expr × Name))

abbrev SubsingletonReprs := RBExprMap Expr

abbrev TodoEntry := Expr × Expr × Expr × Bool

/-- Congruence closure state.
This may be considered to be a set of expressions and an equivalence class over this set.
The equivalence class is generated by the equational rules that are added to the `CCState` and
congruence, that is, if `a = b` then `f(a) = f(b)` and so on. -/
structure CCState where
  entries : Entries := ∅
  parents : Parents := ∅
  congruences : Congruences := ∅
  symmCongruences : SymmCongruences := ∅
  subsingletonReprs : SubsingletonReprs := ∅
  /-- The congruence closure module has a mode where the root of each equivalence class is marked as
      an interpreted/abstract value. Moreover, in this mode proof production is disabled.
      This capability is useful for heuristic instantiation. -/
  frozePartitions : Bool := false
  /-- Returns true if the `CCState` is inconsistent. For example if it had both `a = b` and `a ≠ b`
      in it.-/
  inconsistent := false
  /-- "Global Modification Time". gmt is a number stored on the `CCState`,
      it is compared with the modification time of a cc_entry in e-matching. See `CCState.mt`. -/
  gmt : Nat := 0
  config : CCConfig
#align cc_state Mathlib.Tactic.CC.CCState
#align cc_state.inconsistent Mathlib.Tactic.CC.CCState.inconsistent
#align cc_state.gmt Mathlib.Tactic.CC.CCState.gmt

structure CC where
  state : CCState
  todo : Array TodoEntry := #[]
  /- Porting note: `congruence_closure` in Mathlib3 has more member variables but they're almost
     the copies from `tactic_state`. We translate methods of `congruence_closure` using `TacticM` so
     they are not needed. -/

abbrev CCM := StateRefT CC TacticM

namespace CCM

@[inline]
def run {α : Type} (x : CCM α) (c : CC) : TacticM (α × CC) := StateRefT'.run x c

def add (type : Expr) (proof : Expr) (gen : Nat) : CCM Unit := sorry

end CCM

namespace CCState

open CCM

def mkEntryCore (s : CCState) (e : Expr) (interpreted : Bool) (constructor : Bool) (gen : Nat) :
    CCState :=
  let n : Entry :=
    { next := e
      root := e
      cgRoot := e
      size := 1
      flipped := false
      interpreted
      constructor
      hasLambdas := e.isLambda
      heqProofs := false
      mt := s.gmt
      fo := false
      generation := gen }
  { s with entries := s.entries.insert e n }

def mkCore (config : CCConfig) : CCState :=
  let s : CCState := { config }
  s.mkEntryCore (.const ``True []) true false 0 |>.mkEntryCore (.const ``False []) true false 0
#align cc_state.mk_core Mathlib.Tactic.CC.CCState.mkCore

/-- Create a congruence closure state object using the hypotheses in the current goal. -/
def mkUsingHsCore (cfg : CCConfig) : TacticM CCState := do
  let ctx ← getLCtx
  let ctx ← instantiateLCtxMVars ctx
  let (_, c) ← CCM.run (ctx.forM fun dcl => do
    unless dcl.isImplementationDetail do
      if (← isProp dcl.type) then
       add dcl.type dcl.toExpr 0) { state := mkCore cfg }
  return c.state
#align cc_state.mk_using_hs_core Mathlib.Tactic.CC.CCState.mkUsingHsCore

/-- Get the next element in the equivalence class.
Note that if the given `Expr` `e` is not in the graph then it will just return `e`. -/
def next : CCState → Expr → Expr := sorry
#align cc_state.next Mathlib.Tactic.CC.CCState.next

/-- Returns the root expression for each equivalence class in the graph.
If the `Bool` argument is set to `true` then it only returns roots of non-singleton classes. -/
def rootsCore : CCState → Bool → List Expr := sorry
#align cc_state.roots_core Mathlib.Tactic.CC.CCState.rootsCore

/-- Get the root representative of the given expression. -/
def root : CCState → Expr → Expr := sorry
#align cc_state.root Mathlib.Tactic.CC.CCState.root

/--
"Modification Time". The field m_mt is used to implement the mod-time optimization introduce by the
Simplify theorem prover. The basic idea is to introduce a counter gmt that records the number of
heuristic instantiation that have occurred in the current branch. It is incremented after each round
of heuristic instantiation. The field m_mt records the last time any proper descendant of of thie
entry was involved in a merge. -/
def mt : CCState → Expr → Nat := sorry
#align cc_state.mt Mathlib.Tactic.CC.CCState.mt

/-- Increment the Global Modification time. -/
def incGMT : CCState → CCState := sorry
#align cc_state.inc_gmt Mathlib.Tactic.CC.CCState.incGMT

/-- Check if `e` is the root of the congruence class. -/
def isCgRoot : CCState → Expr → Bool := sorry
#align cc_state.is_cg_root Mathlib.Tactic.CC.CCState.isCgRoot

/-- Pretty print the entry associated with the given expression. -/
def ppEqc : CCState → Expr → MessageData := sorry
#align cc_state.pp_eqc Mathlib.Tactic.CC.CCState.ppEqc

/-- Pretty print the entire cc graph.
If the bool argument is set to true then singleton equivalence classes will be omitted. -/
def ppCore : CCState → Bool → MessageData := sorry
#align cc_state.pp_core Mathlib.Tactic.CC.CCState.ppCore

/-- Add the given expression to the graph. -/
def internalize : CCState → Expr → TacticM CCState := sorry
#align cc_state.internalize Mathlib.Tactic.CC.CCState.internalize

/-- Add the given proof term as a new rule.
The proof term p must be an `Eq _ _`, `HEq _ _`, `Iff _ _`, or a negation of these. -/
def add : CCState → Expr → TacticM CCState := sorry
#align cc_state.add Mathlib.Tactic.CC.CCState.add

/-- Check whether two expressions are in the same equivalence class. -/
def isEqv : CCState → Expr → Expr → TacticM Bool := sorry
#align cc_state.is_eqv Mathlib.Tactic.CC.CCState.isEqv

/-- Check whether two expressions are not in the same equivalence class. -/
def isNotEqv : CCState → Expr → Expr → TacticM Bool := sorry
#align cc_state.is_not_eqv Mathlib.Tactic.CC.CCState.isNotEqv

/-- Returns a proof term that the given terms are equivalent in the given CCState-/
def eqvProof : CCState → Expr → Expr → TacticM Expr := sorry
#align cc_state.eqv_proof Mathlib.Tactic.CC.CCState.eqvProof

/-- `proofFor cc e` constructs a proof for e if it is equivalent to true in `CCState` -/
def proofFor : CCState → Expr → TacticM Expr := sorry
#align cc_state.proof_for Mathlib.Tactic.CC.CCState.proofFor

/-- `refutationFor cc e` constructs a proof for `Not e` if it is equivalent to `False` in `CCState`
-/
def refutationFor : CCState → Expr → TacticM Expr := sorry
#align cc_state.refutation_for Mathlib.Tactic.CC.CCState.refutationFor

/-- If the given state is inconsistent, return a proof for `False`. Otherwise fail. -/
def proofForFalse : CCState → TacticM Expr := sorry
#align cc_state.proof_for_false Mathlib.Tactic.CC.CCState.proofForFalse

def mk' : CCState :=
  CCState.mkCore {}
#align cc_state.mk Mathlib.Tactic.CC.CCState.mk'

def mkUsingHs : TacticM CCState :=
  CCState.mkUsingHsCore {}
#align cc_state.mk_using_hs Mathlib.Tactic.CC.CCState.mkUsingHs

def roots (s : CCState) : List Expr :=
  CCState.rootsCore s true
#align cc_state.roots Mathlib.Tactic.CC.CCState.roots

instance : ToMessageData CCState :=
  ⟨fun s => CCState.ppCore s true⟩

partial def eqcOfCore (s : CCState) (e : Expr) (f : Expr) (r : List Expr) : List Expr :=
    let n := s.next e
    if n == f then e :: r else eqcOfCore s n f (e :: r)
#align cc_state.eqc_of_core Mathlib.Tactic.CC.CCState.eqcOfCore

def eqcOf (s : CCState) (e : Expr) : List Expr :=
  s.eqcOfCore e e []
#align cc_state.eqc_of Mathlib.Tactic.CC.CCState.eqcOf

def inSingletonEqc (s : CCState) (e : Expr) : Bool :=
  s.next e == e
#align cc_state.in_singlenton_eqc Mathlib.Tactic.CC.CCState.inSingletonEqc

def eqcSize (s : CCState) (e : Expr) : Nat :=
  s.eqcOf e |>.length
#align cc_state.eqc_size Mathlib.Tactic.CC.CCState.eqcSize

partial def foldEqcCore {α} (s : CCState) (f : α → Expr → α) (first : Expr) (c : Expr) (a : α) :
    α :=
  let new_a := f a c
  let next := s.next c
  if next == first then new_a else foldEqcCore s f first next new_a
#align cc_state.fold_eqc_core Mathlib.Tactic.CC.CCState.foldEqcCore

def foldEqc {α} (s : CCState) (e : Expr) (a : α) (f : α → Expr → α) : α :=
  foldEqcCore s f e e a
#align cc_state.fold_eqc Mathlib.Tactic.CC.CCState.foldEqc

def mfoldEqc {α} {m : Type → Type} [Monad m] (s : CCState) (e : Expr) (a : α)
    (f : α → Expr → m α) : m α :=
  foldEqc s e (return a) fun act e => do
    let a ← act
    f a e
#align cc_state.mfold_eqc Mathlib.Tactic.CC.CCState.mfoldEqc

end CCState

def ccCore (cfg : CCConfig) : TacticM Unit := do
  evalTactic <| ← `(tactic| intros)
  withMainContext do
    let s ← CCState.mkUsingHsCore cfg
    let t ← getMainTarget
    let s ← s.internalize t
    if s.inconsistent then
        let pr ← s.proofForFalse
        mkAppOptM ``False.elim #[t, pr] >>= closeMainGoal
      else
        let tr := Expr.const ``True []
        let b ← s.isEqv t tr
        if b then
          let pr ← s.eqvProof t tr
          mkAppM ``of_eq_true #[pr] >>= closeMainGoal
        else
          let dbg ← getBoolOption `trace.cc.failure false
          if dbg then
            throwError m!"cc tactic failed, equivalence classes: {s}"
          else
            throwError "cc tactic failed"
#align tactic.cc_core Mathlib.Tactic.CC.ccCore

@[tactic cc]
def cc : Tactic := fun _ =>
  ccCore {}
#align tactic.cc Mathlib.Tactic.CC.cc

#noalign tactic.cc_dbg_core

#noalign tactic.cc_dbg

#align tactic.ac_refl Lean.Meta.AC.acRflTactic

end Mathlib.Tactic.CC
