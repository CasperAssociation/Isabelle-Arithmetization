theory Circuit
  imports Main "LogicCircuitTypes"
begin

class HasPolynomialVariables =
  fixes getPolynomialVariables :: "'a \<Rightarrow> PolynomialVariable set"

(*Note: this covers the LookupArguments instance as a special case*)
instantiation set :: (HasPolynomialVariables) HasPolynomialVariables
begin 
definition getPolynomialVariables_sets :: 
   "'a set \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_sets cs = \<Union> (getPolynomialVariables ` cs)"
instance proof qed
end

instantiation list :: (HasPolynomialVariables) HasPolynomialVariables
begin 
  definition getPolynomialVariables_lists :: 
   "'a list \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_lists cs = getPolynomialVariables (set cs)"
instance proof qed
end

(* Should/can there be a generic map instance?
instantiation (\<rightharpoonup>) :: (type, type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_map where
"getPolynomialVariables_map cs = {}"
instance proof qed
end
*)

instantiation PowerProduct_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_PowerProduct :: 
  "PowerProduct \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_PowerProduct p = 
  {key. \<exists>y . unPowerProduct p key = Some y}"
  instance proof qed
end

instantiation Polynomial_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_Polynomial :: 
  "Polynomial \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_Polynomial p = 
  getPolynomialVariables {key. \<exists>y . unPolynomial p key = Some y}"
  instance proof qed
end

instantiation PolynomialConstraints_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_PolynomialConstraints :: 
  "PolynomialConstraints \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_PolynomialConstraints cs = 
  getPolynomialVariables (map snd (constraints cs))"
  instance proof qed
end

instantiation Term :: HasPolynomialVariables
begin
  fun getPolynomialVariablesTerm ::
  "Term \<Rightarrow> PolynomialVariable set"where
  "getPolynomialVariablesTerm (Var x) = {x}" |
  "getPolynomialVariablesTerm (Lookup is x) = 
    \<Union> (set (map (getPolynomialVariablesTerm \<circ> fst) is))
    \<union> {\<lparr> colIndex = x, rowIndex = 0 \<rparr>}" |
  "getPolynomialVariablesTerm (Const _) = {}" |
  "getPolynomialVariablesTerm (Plus x y) = 
    getPolynomialVariablesTerm x \<union> getPolynomialVariablesTerm y" |
  "getPolynomialVariablesTerm (Times x y) = 
    getPolynomialVariablesTerm x \<union> getPolynomialVariablesTerm y" |
  "getPolynomialVariablesTerm (Max x y) = 
    getPolynomialVariablesTerm x \<union> getPolynomialVariablesTerm y" |
  "getPolynomialVariablesTerm (IndLess x y) = 
    getPolynomialVariablesTerm x \<union> getPolynomialVariablesTerm y"
  instance proof qed
end

instantiation AtomicLogicConstraint :: HasPolynomialVariables
begin
  primrec getPolynomialVariablesALC ::
  "AtomicLogicConstraint \<Rightarrow> PolynomialVariable set" where
  "getPolynomialVariablesALC (Equals x y) = 
    getPolynomialVariables x \<union> getPolynomialVariables y" |
  "getPolynomialVariablesALC (LessThan x y) = 
    getPolynomialVariables x \<union> getPolynomialVariables y"
  instance proof qed
end

instantiation LogicConstraint :: HasPolynomialVariables
begin
  fun getPolynomialVariablesLC ::
  "LogicConstraint \<Rightarrow> PolynomialVariable set" where
  "getPolynomialVariablesLC (Atom x) = getPolynomialVariables x" |
  "getPolynomialVariablesLC (Not x) = getPolynomialVariablesLC x" |
  "getPolynomialVariablesLC (And x y) = 
    getPolynomialVariablesLC x \<union> getPolynomialVariablesLC y" |
  "getPolynomialVariablesLC (Or x y) = 
    getPolynomialVariablesLC x \<union> getPolynomialVariablesLC y" |
  "getPolynomialVariablesLC (Iff x y) = 
    getPolynomialVariablesLC x \<union> getPolynomialVariablesLC y" |
  "getPolynomialVariablesLC Top = {}" |
  "getPolynomialVariablesLC Bottom = {}"
  instance proof qed
end

instantiation LogicConstraints_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_LogicConstraints :: 
  "LogicConstraints \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_LogicConstraints cs = 
  getPolynomialVariables (map snd (LogicConstraints.constraints cs))"
  instance proof qed
end

instantiation LookupArgument_ext :: (HasPolynomialVariables, type) HasPolynomialVariables 
begin
definition getPolynomialVariables_LookupArgument ::
  "'a LookupArgument \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_LookupArgument x = 
  getPolynomialVariables (gate x) \<union>
  getPolynomialVariables (map fst (tableMap x))"
instance proof qed
end

instantiation Circuit_ext :: (HasPolynomialVariables, HasPolynomialVariables, type) HasPolynomialVariables 
begin
definition getPolynomialVariables_Circuit ::
  "('a, 'b) Circuit \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_Circuit x = 
  getPolynomialVariables (Circuit.gateConstraints x) \<union>
  getPolynomialVariables (Circuit.lookupArguments x)"
instance proof qed
end

class HasScalars =
  fixes getScalars :: "'a \<Rightarrow> Scalar set"

(*Note: this covers the LookupArguments instance as a special case*)
instantiation set :: (HasScalars) HasScalars
begin 
  definition getScalars_sets :: 
  "'a set \<Rightarrow> Scalar set" where
"getScalars_sets cs = \<Union> (getScalars ` cs)"
instance proof qed
end

instantiation list :: (HasScalars) HasScalars
begin 
  definition getScalars_lists :: 
  "'a list \<Rightarrow> Scalar set" where
"getScalars_lists cs = getScalars (set cs)"
instance proof qed
end

instantiation Polynomial_ext :: (type) HasScalars
begin 
  definition getScalars_Polynomial :: 
  "Polynomial \<Rightarrow> Scalar set" where
"getScalars_Polynomial p = {v. \<exists>key. unPolynomial p key = Some v}"
  instance proof qed
end

instantiation Term :: HasScalars
begin
  fun getScalarsTerm :: 
  "Term \<Rightarrow> Scalar set" where
  "getScalarsTerm (Var x) = {}" |
  "getScalarsTerm (Lookup is x) = 
    \<Union> (set (map (getScalarsTerm \<circ> fst) is))" |
  "getScalarsTerm (Const x) = {x}" |
  "getScalarsTerm (Plus x y) = 
    getScalarsTerm x \<union> getScalarsTerm y" |
  "getScalarsTerm (Times x y) = 
    getScalarsTerm x \<union> getScalarsTerm y" |
  "getScalarsTerm (Max x y) = 
    getScalarsTerm x \<union> getScalarsTerm y" |
  "getScalarsTerm (IndLess x y) = 
    getScalarsTerm x \<union> getScalarsTerm y"
  instance proof
  qed
end

instantiation AtomicLogicConstraint :: HasScalars
begin
  primrec getScalarsALC :: 
  "AtomicLogicConstraint \<Rightarrow> Scalar set" where
  "getScalarsALC (Equals x y) = 
    getScalars x \<union> getScalars y" |
  "getScalarsALC (LessThan x y) = 
    getScalars x \<union> getScalars y"
  instance proof
  qed
end

instantiation LogicConstraint :: HasScalars
begin
  fun getScalarsLC :: 
  "LogicConstraint \<Rightarrow> Scalar set" where
  "getScalarsLC (Atom x) = getScalars x" |
  "getScalarsLC (Not x) = getScalarsLC x" |
  "getScalarsLC (And x y) = 
    getScalarsLC x \<union> getScalarsLC y" |
  "getScalarsLC (Or x y) = 
    getScalarsLC x \<union> getScalarsLC y" |
  "getScalarsLC (Iff x y) = 
    getScalarsLC x \<union> getScalarsLC y" |
  "getScalarsLC Top = {1}" |
  "getScalarsLC Bottom = {0}"
  instance proof
  qed
end

instantiation LogicConstraints_ext :: (type) HasScalars
begin 
  definition getScalars_LogicConstraints :: 
  "LogicConstraints \<Rightarrow> Scalar set" where
"getScalars_LogicConstraints cs = 
  getScalars (map snd (LogicConstraints.constraints cs))"
  instance proof qed
end

instantiation LookupArgument_ext :: (HasScalars, type) HasScalars 
begin
definition getScalars_LookupArgument ::
  "'a LookupArgument \<Rightarrow> Scalar set" where
"getScalars_LookupArgument x = 
  getScalars (gate x) \<union>
  getScalars (map fst (tableMap x))"
instance proof qed
end

instantiation Circuit_ext :: (HasScalars, HasScalars, type) HasScalars 
begin
definition getScalars_Circuit ::
  "('a, 'b) Circuit \<Rightarrow> Scalar set" where
"getScalars_Circuit x = 
  getScalars (Circuit.gateConstraints x) \<union>
  getScalars (Circuit.lookupArguments x)"
instance proof qed
end




locale HasEvaluate =
  fixes evaluate :: "Argument \<Rightarrow> 'a \<rightharpoonup> 'b"



definition performLookups :: "
  (Argument \<Rightarrow> (RowCount * 'a) \<Rightarrow> (RowIndex \<rightharpoonup> (Scalar option)) option) \<Rightarrow>
  RowCount \<Rightarrow>
  Argument \<Rightarrow>
  ('a InputExpression * LookupTableColumn) list \<Rightarrow>
  LookupTableOutputColumn \<Rightarrow>
  (RowIndex \<rightharpoonup> (Scalar option)) option" where
"performLookups eval rc arg is outCol = None"




(*
performLookups ::
  HasEvaluate (RowCount, a) (Map (RowIndex 'Absolute) (Maybe Scalar)) =>
  ann ->
  RowCount ->
  Argument ->
  [(InputExpression a, LookupTableColumn)] ->
  LookupTableOutputColumn ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Maybe Scalar))
performLookups ann rc arg is outCol = do
  inputTable <-
    fmap (Map.mapMaybe id)
      <$> mapM (evaluate ann arg . (rc,) . (^. #getInputExpression) . fst) is
  results <-
    getLookupResults
      ann
      rc
      Nothing
      (getCellMap arg)
      (zip inputTable (snd <$> is))
  let allRows = getRowSet rc Nothing
      results' =
        fmap Just . Map.mapKeys (^. #rowIndex) $
          Map.filterWithKey (\k _ -> k ^. #colIndex == outCol') results
  pure $ results' <> Map.fromList ((,Nothing) <$> Set.toList allRows)
  where
    outCol' = outCol ^. #unLookupTableOutputColumn . #unLookupTableColumn
*)


end