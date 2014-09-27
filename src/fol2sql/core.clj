(ns fol2sql.core
  (:require [clojure.core.match :refer [match]]
            [clojure.set :as set]))

(comment
  "FoL syntax in clojure"
  (foo x y) => "select x, y from foo"
  (exists [x] (foo x y)) => "select distinct y from foo"
  (and (foo x y) (bar y z)) => "select foo.x, foo.y, bar.z from foo join bar on foo.y = bar.y"
  (forall [x] (implies (man x) (mortal x)))
  =>  (not (exists [x] (and (man x) (not (mortal x))))) =>
  "select true where not exists (select x from man where x not in (select x from mortal))"


  ;; select the set of eaters who eat every food.
  (and
   (exists [x] (eats x y))
   (forall [x] (implies (food x)
                        (eats x y))))
  "select distinct y from eats where not exists
    (select food from food where food not in (select food from eats where eats.person = y)"

  Analogies
  First-order logic           / SQL
  Base predicate name         / Table
  instance of ^ in expression / Distinct alias of table
  Comparsion predicate        / Comparison operator
  Derived predicate           / Query, subquery or view
  Argument slot of predicate  / Column of table/view/subquery
  Variable                    / Set of equated columns of tables or their aliases
  and                         / and
  or                          / union, or
  not                         / not
  exists x                    / select distinct <all columns but x>, exists (select x from ...)
  forall x                    / not in (select ... where not exists (select x from ...))
  )

(defn desugar
  "Desugars the expression recursively to eliminate all implies and forall:

   (implies X Y) => (or (not X) Y)
   (forall [x] Y) => (not (exists [x] (not Y)))

   Most other functions assume desugared expressions as input."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply list 'and (map desugar clauses))

         [(('or & clauses) :seq)]
         (apply list 'or (map desugar clauses))

         [(('implies hypothesis conclusion) :seq)]
         (list 'or (list 'not (desugar hypothesis)) (desugar conclusion))

         [(('not inner) :seq)]
         (list 'not (desugar inner))

         [(('exists [var] inner) :seq)]
         (list 'exists [var] (desugar inner))

         [(('forall [var] inner) :seq)]
         (list 'not (list 'exists [var] (list 'not (desugar inner))))

         [atom] atom))

(defn normalize
  " Applies these negation-related rewrite rules as far as possible:

     double negation elimination:
     (not (not X)) => X

     pushing negations inside and/or. (Note we could push them inside
     an exists, but that would create a forall which we want to
     avoid.)
     (not (and X Y)) => (or (not X) (not Y))
     (not (or X Y)) => (and (not X) (not Y))

     flattens nested ands and ors:
     (and (and x y) (and a b) c) => (and x y a b c)
     (or (or x y) (or a b) c) => (or x y a b c)

     Assumes input has been desguared.

     In the result, a not will only ever appear around an exists, or around an base predicate.

     an and will never be nested directly inside an and, and likewise
     for or. Although note we don't go the whole hog and convert these
     boolean expressions to CNF or DNF. If we went to DNF we'd have
     something expressible via datalog-style horn clauses."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply list 'and (mapcat (fn [clause]
                                    (let [norm-clause (normalize clause)]
                                      (match [norm-clause]
                                             [(('and & nested-clauses) :seq)] nested-clauses
                                             :else [norm-clause])))
                                  clauses))

         [(('or & clauses) :seq)]
         (apply list 'or (mapcat (fn [clause]
                                   (let [norm-clause (normalize clause)]
                                     (match [norm-clause]
                                            [(('or & nested-clauses) :seq)] nested-clauses
                                            :else [norm-clause])))
                                 clauses))

         [(('not (('not inner) :seq)) :seq)]
         (normalize inner)

         [(('not (('and & clauses) :seq)) :seq)]
         (apply list 'or (map #(normalize (list 'not %)) clauses))

         [(('not (('or & clauses) :seq)) :seq)]
         (apply list 'and (map #(normalize (list 'not %)) clauses))

         [(('not inner) :seq)]
         (list 'not (normalize inner))

         [(('exists [var] inner) :seq)]
         (list 'exists [var] (normalize inner))

         [atom] atom))

(defn free-vars
  "Returns the free variables in the expression.
   Also checks and complains if a quantifier within it tries to close over a non-free variable."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply set/union (map free-vars clauses))

         [(('or & clauses) :seq)]
         (apply set/union (map free-vars clauses))

         [(('implies hypothesis conclusion) :seq)]
         (set/union (free-vars hypothesis) (free-vars conclusion))

         [(('not inner) :seq)]
         (free-vars inner)

         [(('exists [var] inner) :seq)]
         (let [inner-free-vars (free-vars inner)]
           (if (contains? inner-free-vars var)
             (set/difference inner-free-vars #{var})
             (throw (IllegalArgumentException.
                     (str "Quantifier can't close over variable " var
                          " which isn't free in inner expression " inner)))))

         [(('forall [var] inner) :seq)]
         (let [inner-free-vars (free-vars inner)]
           (if (contains? inner-free-vars var)
             (set/difference inner-free-vars #{var})
             (throw (IllegalArgumentException.
                     (str "Quantifier can't close over variable " var
                          " which isn't free in inner expression " inner)))))

         [((predicate & arguments) :seq)]
         (set arguments)))

(def unsafe-predicate?
  "Special predicates which aren't in general represented by finite
  relations and aren't safe. (In sql, these are built-in comparison
  operators rather than tables)"
  '#{= != < > >= <= })

(defn negated-safe?
  [expr]
  (match [expr]
         [(('not inner) :seq)] (safe? inner)
         :else false))

(defn safe?
  "Checks to see if a desguared and normalized expression is 'safe'
  and able to be mapped to relational algebra or sql queries.

  Safeness implies that there will be finitely many tuples satisfying
  it, but also a stronger property: that its interpretation doesn't
  depend on any assumptions about the full set of values in the domain
  which unrestrcited free variables range over."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (let [vars (free-vars expr)
               safe-vars (apply set/union (map free-vars (filter safe? clauses)))]
           ;; every free variable must be present in at least one safe
           ;; clause (TODO: or is implied by the expression to be
           ;; equal to a variable which is in a safe clause; would
           ;; need to further normalize the expression (say to CNF) to
           ;; determine this I think).
           ;; any unsafe clauses must be negations of safe clauses.
           (and (= vars safe-vars)
                (every? negated-safe? (filter (comp not safe?) clauses))))

         [(('or & clauses) :seq)]
         (let [vars (free-vars expr)]
           ;; every clause must be safe and every clause must
           ;; reference (hence restrict to be safe) every free variable.
           (every? (fn [clause]
                     (and (safe? clause)
                          (= (free-vars clause) vars)))
                   clauses))

         [(('not inner) :seq)]
         ;; a not expression can only be safe if it has no free
         ;; variables, otherwise the variables could range over the
         ;; entire (unspecified, possibly infinite) domain, minus the
         ;; rows satisfying the inner expression, hence could in
         ;; general be infinite and depnds on what is in the overall
         ;; domain (which we want to avoid any dependence on).
         ;; Even if there are no free variables, the inner expression
         ;; needs to be safe too, otherwise we could have things like:
         ;; (not (exists [a] (= a a)))
         ;; which isn't translatable into SQL and depends on what's in
         ;; the domain (the example asserts the domain is empty)
         (and (empty? (free-vars inner))
              (safe? inner))

         [(('exists [var] inner) :seq)]
         ;; this is like requiring that the quantifier is restricted,
         ;; i.e. "exists x in foo such that"
         (safe? inner)

         [((predicate & arguments) :seq)]
         (not (unsafe-predicate? predicate))))
