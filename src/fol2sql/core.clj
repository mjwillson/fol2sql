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
    (select food from food where food not in (select food from eats where eats.person = y)")

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

     Assumes input has been desguared.

     In the result, a not will only ever appear around an exists, or around an base predicate."
  [expr]
  (match [expr]
         [(('and & clauses) :seq)]
         (apply list 'and (map normalize clauses))

         [(('or & clauses) :seq)]
         (apply list 'or (map normalize clauses))

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

(defn finite?
  "Checks to see if a desguared and normalized expression can be
  statically guaranteed to be finite, under the assumption that all
  base predicates are finite (as they would be in case of a finite
  database of facts.)

  Sentences which meet this constraint can be expressed as datalog
  and as SQL queries"
  [expr]
  (match [expr]
         [(('and & clauses) :seq)] (boolean (some finite? clauses))
         [(('or & clauses) :seq)] (every? finite? clauses)
         [(('not inner) :seq)] false
         [(('exists [var] inner) :seq)] (finite? inner)
         [atom] true))

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

;; datalog:
;; derived predicate is an existentially-quantified DNF expression
;; over other predicates. Each disjunctive clause must include one
;; non-negated term
