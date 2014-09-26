# fol2sql

Ocassionally I like to claim in a rather handwavey fashion that the relational algebra (and discrepancies aside, SQL) are basically just an alternative syntax for first-order logic.

A statement in first-order logic with some free variables, corresponds to a query whose resultset contains a column for each of these free variables. A predicate corresponds to a table or relation.

This project is a bit of code to actually demonstrate this by translating sentences in FoL into SQL statements. (Going in the reverse direction is possible too if you stick to a well-behaved subset of SQL, but I don't attempt this here).