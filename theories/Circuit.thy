theory Circuit
  imports Main "LogicCircuitTypes"
begin

class HasPolynomialVariables =
  fixes getPolynomialVariables :: "'a \<Rightarrow> PolynomialVariable set"

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
  \<Union> (getPolynomialVariables ` {key. \<exists>y . unPolynomial p key = Some y})"
  instance proof qed
end

instantiation PolynomialConstraints_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_PolynomialConstraints :: 
  "PolynomialConstraints \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_PolynomialConstraints cs = 
  \<Union> ((getPolynomialVariables \<circ> snd) ` set (constraints cs))"
  instance proof qed
end

instantiation Term :: HasPolynomialVariables
begin
  fun getPolynomialVariablesTerm where
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
  primrec getPolynomialVariablesALC where
  "getPolynomialVariablesALC (Equals x y) = 
    getPolynomialVariables x \<union> getPolynomialVariables y" |
  "getPolynomialVariablesALC (LessThan x y) = 
    getPolynomialVariables x \<union> getPolynomialVariables y"
  instance proof qed
end

instantiation LogicConstraint :: HasPolynomialVariables
begin
  fun getPolynomialVariablesLC where
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


class HasScalars =
  fixes getScalars :: "'a \<Rightarrow> Scalar set"

instantiation Term :: HasScalars
begin
  fun getScalarsTerm where
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
  primrec getScalarsALC where
  "getScalarsALC (Equals x y) = 
    getScalars x \<union> getScalars y" |
  "getScalarsALC (LessThan x y) = 
    getScalars x \<union> getScalars y"
  instance proof
  qed
end

instantiation LogicConstraint :: HasScalars
begin
  fun getScalarsLC where
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
*)

(*
instantiation 'a LookupArgument :: HasScalars
begin
  
end
*)

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