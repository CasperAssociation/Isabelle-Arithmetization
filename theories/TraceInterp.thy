theory TraceInterp
  imports Main "LogicCircuitTypes"
begin

definition EqualityConstrainableConstraint :: "TraceType \<Rightarrow> bool" where
  "EqualityConstrainableConstraint c = (\<forall> x .
    ListMem x (TraceType.equalityConstraints c) \<longrightarrow> (
    \<forall> co. co \<in> x \<longrightarrow>
    colIndex co \<in> TraceType.equalityConstrainableColumns c
  ))"

definition EqualityConstraint :: "TraceType \<Rightarrow> InputMatrix \<Rightarrow> bool" where
  "EqualityConstraint c m = (\<forall> x .
    ListMem x (TraceType.equalityConstraints c) \<longrightarrow> (
    \<forall> c1 c2 b1 b2 .
    \<lparr> colIndex = c1, rowIndex = c2 \<rparr> \<in> x \<and>
    \<lparr> colIndex = b1, rowIndex = b2 \<rparr> \<in> x \<longrightarrow> (
    \<exists> c b . m c1 = Some c \<and> m b1 = Some b \<and>
    c ! nat (c2 mod of_nat (length c)) = 
    b ! nat (b2 mod of_nat (length b))
  )))"

end