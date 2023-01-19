theory CircuitInterp
  imports Main "LogicCircuitTypes"
begin

definition FixedTypeConstraint :: "('a, 'b) Circuit \<Rightarrow> bool" where
  "FixedTypeConstraint c = (\<forall> x .
    (\<exists> y. Circuit.fixedValues c x = Some y) \<longrightarrow> (
    Circuit.columnTypes c x = Some Fixed
  ))"

definition FixedConstraint :: "('a, 'b) Circuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "FixedConstraint c m = (\<forall> x .
  (case (m x, Circuit.fixedValues c x) of
    (Some x', Some y') \<Rightarrow> (x' = y') |
    _ \<Rightarrow> True))"

definition EqualityConstrainableConstraint :: "('a, 'b) Circuit \<Rightarrow> bool" where
  "EqualityConstrainableConstraint c = (\<forall> x .
    ListMem x (Circuit.equalityConstraints c) \<longrightarrow> (
    \<forall> co. co \<in> x \<longrightarrow>
    colIndex co \<in> Circuit.equalityConstrainableColumns c
  ))"

definition EqualityConstraint :: "('a, 'b) Circuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "EqualityConstraint c m = (\<forall> x .
    ListMem x (Circuit.equalityConstraints c) \<longrightarrow> (
    \<forall> c1 c2 b1 b2 .
    \<lparr> colIndex = c1, rowIndex = c2 \<rparr> \<in> x \<and>
    \<lparr> colIndex = b1, rowIndex = b2 \<rparr> \<in> x \<longrightarrow> (
    \<exists> c b . m c1 = Some c \<and> m b1 = Some b \<and>
    c ! nat (c2 mod of_nat (length c)) = 
    b ! nat (b2 mod of_nat (length b))
  )))"

definition RowCountConstraint :: "('a, 'b) Circuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "RowCountConstraint c m = (\<forall> ci co.
    m ci = Some co \<longrightarrow>
    of_nat (length co) = Circuit.rowCount c
  )"

definition LogicBoundsConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "LogicBoundsConstraint c m = (\<forall> ci co.
    m ci = Some co \<longrightarrow> (
    \<exists> b. bounds (Circuit.gateConstraints c) ci = Some b \<and> (
    \<forall> e. ListMem e co \<longrightarrow> \<bar>e\<bar> < of_nat b
  )))"

definition varMap :: "InputMatrix \<Rightarrow> PolynomialVariable \<rightharpoonup> Scalar" where
  "varMap m co = 
  (case m (colIndex co) of
    Some x \<Rightarrow> Some (x ! nat (rowIndex co mod of_nat (length x))) |
    _ \<Rightarrow> None)"

fun termInterp :: "Term \<Rightarrow> InputMatrix \<rightharpoonup> Scalar" where
"termInterp (Var x) mp = varMap mp x" |

(*
  TODO: Implement this?
  Lookup
      "(Term InputExpression * LookupTableColumn) list"
      LookupTableOutputColumn |
*)
"termInterp (Lookup tbl cl) mp = 
  (case mp cl of
    Some _ \<Rightarrow> None |
    _ \<Rightarrow> None
  )" |

"termInterp (Const x) mp = Some x" |
"termInterp (Plus x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some ((x' + y') mod GoldilocksSize) |
    _ \<Rightarrow> None)" |
"termInterp (Times x y) mp = 
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some ((x' * y') mod GoldilocksSize) |
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

term rotate
value "rotate (length [a, b, c, d] - 1) [a, b, c, d]"


definition rowMap :: "InputMatrix \<Rightarrow> PolynomialVariable \<rightharpoonup> Scalar list" where
  "rowMap m co = 
  (case m (colIndex co) of
    Some row \<Rightarrow> Some (
      rotate (length row - nat (rowIndex co mod of_nat (length row))) row
    ) |
    _ \<Rightarrow> None)"

fun termInterpRow :: "RowCount \<Rightarrow> Term \<Rightarrow> InputMatrix \<rightharpoonup> Scalar list" where
"termInterpRow rc (Var x) mp = rowMap mp x" |

(*
  TODO: Implement this?
  Lookup
      "(Term InputExpression * LookupTableColumn) list"
      LookupTableOutputColumn |
*)
"termInterpRow rc (Lookup tbl cl) mp = 
  (case mp cl of
    Some _ \<Rightarrow> None |
    _ \<Rightarrow> None
  )" |

"termInterpRow rc (Const x) mp = Some (replicate (nat (rc mod GoldilocksSize)) x)" |
"termInterpRow rc (Plus x y) mp = 
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). (a + b) mod GoldilocksSize) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"termInterpRow rc (Times x y) mp = 
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). (a * b) mod GoldilocksSize) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"termInterpRow rc (Max x y) mp = 
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). max a b) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"termInterpRow rc (IndLess x y) mp = 
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). (if a < b then 1 else 0)) (zip x' y')
    ) |
    _ \<Rightarrow> None)"

fun ALCInterp :: "AtomicLogicConstraint \<Rightarrow> InputMatrix \<rightharpoonup> bool" where
"ALCInterp (Equals x y) mp =
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' = y') |
    _ \<Rightarrow> None)" |
"ALCInterp (LessThan x y) mp =
  (case (termInterp x mp, termInterp y mp) of
    (Some x', Some y') \<Rightarrow> Some (x' < y') |
    _ \<Rightarrow> None)"

fun ALCInterpRow :: "RowCount \<Rightarrow> AtomicLogicConstraint \<Rightarrow> InputMatrix \<rightharpoonup> bool list" where
"ALCInterpRow rc (Equals x y) mp =
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). a = b) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"ALCInterpRow rc (LessThan x y) mp =
  (case (termInterpRow rc x mp, termInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). a < b) (zip x' y')
    ) |
    _ \<Rightarrow> None)"

fun LCInterp :: "LogicConstraint \<Rightarrow> InputMatrix \<rightharpoonup> bool" where
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

fun LCInterpRow :: "RowCount \<Rightarrow> LogicConstraint \<Rightarrow> InputMatrix \<rightharpoonup> bool list" where
"LCInterpRow rc (Atom x) mp = ALCInterpRow rc x mp" |
"LCInterpRow rc (Not x) mp = 
  (case LCInterpRow rc x mp of
    Some x' \<Rightarrow> Some (map (\<lambda>a. \<not> a) x') |
    _ \<Rightarrow> None)" |
"LCInterpRow rc (And x y) mp = 
  (case (LCInterpRow rc x mp, LCInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). a & b) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"LCInterpRow rc (Or x y) mp = 
  (case (LCInterpRow rc x mp, LCInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). a | b) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"LCInterpRow rc (Iff x y) mp = 
  (case (LCInterpRow rc x mp, LCInterpRow rc y mp) of
    (Some x', Some y') \<Rightarrow> Some (
      map (\<lambda>(a, b). a \<longleftrightarrow> b) (zip x' y')
    ) |
    _ \<Rightarrow> None)" |
"LCInterpRow rc Top mp = Some (replicate (nat (rc mod GoldilocksSize)) True)" |
"LCInterpRow rc Bottom mp = Some (replicate (nat (rc mod GoldilocksSize)) False)"

(*
definition LogicGateConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "LogicGateConstraint c m = (
    \<forall> l g. ListMem (l, g) (LogicConstraints.constraints (Circuit.gateConstraints c)) \<longrightarrow>
    LCInterp g m = Some True
  )"
*)

definition LogicGateConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "LogicGateConstraint c m = (
    \<forall> l g. ListMem (l, g) (LogicConstraints.constraints (Circuit.gateConstraints c)) \<longrightarrow> (
    \<forall> j. 0 \<le> j \<and> j < Circuit.rowCount c \<longrightarrow>
    LCInterpRow (Circuit.rowCount c) g m =
    Some (replicate (nat (Circuit.rowCount c mod GoldilocksSize)) True)
  ))"

(*
(* The lookup constraints outside the gate check go unused in a logic circuit *)
definition LogicLookupConstraint :: "LogicCircuit \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "LogicLookupConstraint c m = (
    \<forall> x y z. \<lparr> label = x, gate = y, tableMap = z \<rparr> \<in> Circuit.lookupArguments c \<longrightarrow>
    True
  )"
*) 

end