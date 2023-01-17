theory CircuitInterp
  imports Main "LogicCircuitTypes"
begin

type_synonym InputMatrix = "ColumnIndex \<rightharpoonup> FixedColumn"

definition FixedTypeConstraint :: "LogicCircuit \<Rightarrow> bool" where
  "FixedTypeConstraint c = (\<forall> x .
    (\<exists> y. Circuit.fixedValues c x = Some y) \<longrightarrow> (
    Circuit.columnTypes c x = Some Fixed
  ))"

definition FixedConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "FixedConstraint c m = (\<forall> x .
  (case (m x, Circuit.fixedValues c x) of
    (Some x', Some y') \<Rightarrow> (x' = y') |
    _ \<Rightarrow> True))"

definition EqualityConstrainableConstraint :: "LogicCircuit \<Rightarrow> bool" where
  "EqualityConstrainableConstraint c = (\<forall> x .
    ListMem x (Circuit.equalityConstraints c) \<longrightarrow> (
    \<forall> co. co \<in> x \<longrightarrow>
    colIndex co \<in> Circuit.equalityConstrainableColumns c
  ))"

definition EqualityConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "EqualityConstraint c m = (\<forall> x .
    ListMem x (Circuit.equalityConstraints c) \<longrightarrow> (
    \<forall> c1 c2 b1 b2 .
    \<lparr> colIndex = c1, rowIndex = c2 \<rparr> \<in> x \<and>
    \<lparr> colIndex = b1, rowIndex = b2 \<rparr> \<in> x \<longrightarrow> (
    \<exists> c b . m c1 = Some c \<and> m b1 = Some b \<and>
    c ! nat (c2 mod of_nat (length c)) = 
    b ! nat (b2 mod of_nat (length b))
  )))"






definition ofan :: "('b \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'c option" where
  "ofan op rc x y = 
  (case (rc x, rc y) of
    (Some x', Some y') \<Rightarrow> Some (op x' y') |
    _ \<Rightarrow> None)"

fun termInterp :: "Term \<Rightarrow> (PolynomialVariable \<rightharpoonup> Scalar) \<Rightarrow> Scalar option" where
"termInterp (Var x) mp = mp x" |

(*
  TODO: Implement this?
  Lookup
      "(Term InputExpression * LookupTableColumn) list"
      LookupTableOutputColumn |
*)
"termInterp (Lookup tbl cl) mp = None" |

"termInterp (Const x) mp = Some x" |
"termInterp (Plus x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' + y') |
    _ \<Rightarrow> None)" |
"termInterp (Times x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' * y') |
    _ \<Rightarrow> None)" |
"termInterp (Max x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (max x' y') |
    _ \<Rightarrow> None)" |
"termInterp (IndLess x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> 
      Some (if x' < y' then 1 else 0) |
    _ \<Rightarrow> None)"

fun ALCInterp :: "AtomicLogicConstraint \<Rightarrow> (PolynomialVariable \<rightharpoonup> Scalar) \<Rightarrow> bool option" where
"ALCInterp (Equals x y) mp =
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' = y') |
    _ \<Rightarrow> None)" |
"ALCInterp (LessThan x y) mp =
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' < y') |
    _ \<Rightarrow> None)"

fun LCInterp :: "LogicConstraint \<Rightarrow> (PolynomialVariable \<rightharpoonup> Scalar) \<Rightarrow> bool option" where
"LCInterp (Atom x) mp = ALCInterp x mp" |
"LCInterp (Not x) mp = 
  (case LCInterp x mp of
    Some x' \<Rightarrow> Some (\<not> x') |
    _ \<Rightarrow> None)" |
"LCInterp (And x y) mp = 
  (case (LCInterp x mp, LCInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' & y') |
    _ \<Rightarrow> None)" |
"LCInterp (Or x y) mp = 
  (case (LCInterp x mp, LCInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' | y') |
    _ \<Rightarrow> None)" |
"LCInterp (Iff x y) mp = 
  (case (LCInterp x mp, LCInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' \<longleftrightarrow> y') |
    _ \<Rightarrow> None)" |
"LCInterp Top mp = Some True" |
"LCInterp Bottom mp = Some False"



end