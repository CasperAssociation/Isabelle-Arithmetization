theory Circuit_Map
  imports Main "LogicCircuitTypes_Map"
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
  {key. \<exists>y . (key, y) \<in> set (unPowerProduct p)}"
  instance proof qed
end

instantiation Polynomial_ext :: (type) HasPolynomialVariables
begin 
  definition getPolynomialVariables_Polynomial :: 
  "Polynomial \<Rightarrow> PolynomialVariable set" where
"getPolynomialVariables_Polynomial p = 
  getPolynomialVariables {key. \<exists>y . map_of (unPolynomial p) key = Some y}"
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
"getScalars_Polynomial p = {v. \<exists>key. map_of (unPolynomial p) key = Some v}"
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

(*
locale HasLookupArguments =
  fixes getLookupArguments :: "'a \<Rightarrow> 'b LookupArguments"
*)
type_synonym ('a, 'b) HasLookupArguments = "'a \<Rightarrow> 'b LookupArguments"

fun getLookupArguments_List ::
  "('a, 'b) HasLookupArguments \<Rightarrow>
   ('a list, 'b) HasLookupArguments" where
"getLookupArguments_List gLA = \<Union> \<circ> set \<circ> map gLA"

fun getLookupArguments_Term_Term ::
  "(Term, Term) HasLookupArguments" where
"getLookupArguments_Term_Term (Const x) = {}" |
"getLookupArguments_Term_Term (Var x) = {}" |
"getLookupArguments_Term_Term (Lookup is oo) = 
  {\<lparr> label = ''application'', gate = Const 0, tableMap = [(Const 0, oo)]\<rparr>} \<union>
  \<Union> (set (map (getLookupArguments_Term_Term \<circ> fst) is))" |
"getLookupArguments_Term_Term (Plus x y) = 
  getLookupArguments_Term_Term x \<union>
  getLookupArguments_Term_Term y" |
"getLookupArguments_Term_Term (Times x y) = 
  getLookupArguments_Term_Term x \<union>
  getLookupArguments_Term_Term y" |
"getLookupArguments_Term_Term (Max x y) = 
  getLookupArguments_Term_Term x \<union>
  getLookupArguments_Term_Term y"|
"getLookupArguments_Term_Term (IndLess x y) = 
  getLookupArguments_Term_Term x \<union>
  getLookupArguments_Term_Term y"

fun getLookupArguments_LogicConstraint_Term ::
  "(LogicConstraint, Term) HasLookupArguments" where
"getLookupArguments_LogicConstraint_Term (Atom c) = 
  (case c of
    (Equals x y) \<Rightarrow> 
      getLookupArguments_Term_Term x \<union>
      getLookupArguments_Term_Term y |
    (LessThan x y) \<Rightarrow> 
      getLookupArguments_Term_Term x \<union>
      getLookupArguments_Term_Term y
  )" |
"getLookupArguments_LogicConstraint_Term (Not p) = 
  getLookupArguments_LogicConstraint_Term p" |
"getLookupArguments_LogicConstraint_Term (And p q) =  
  getLookupArguments_LogicConstraint_Term p \<union>
  getLookupArguments_LogicConstraint_Term q" |
"getLookupArguments_LogicConstraint_Term (Or p q) =  
  getLookupArguments_LogicConstraint_Term p \<union>
  getLookupArguments_LogicConstraint_Term q" |
"getLookupArguments_LogicConstraint_Term (Iff p q) = 
  getLookupArguments_LogicConstraint_Term p \<union>
  getLookupArguments_LogicConstraint_Term q" |
"getLookupArguments_LogicConstraint_Term Top = {}" |
"getLookupArguments_LogicConstraint_Term Bottom = {}"


fun getLookupArguments_LogicCircuit_Term ::
  "(LogicCircuit, Term) HasLookupArguments" where
"getLookupArguments_LogicCircuit_Term c =
  Circuit.lookupArguments c \<union>
  getLookupArguments_List getLookupArguments_LogicConstraint_Term 
    (map snd (LogicConstraints.constraints (Circuit.gateConstraints c)))"

fun getLookupTables ::
  "('a, 'b) HasLookupArguments \<Rightarrow>
   'a \<Rightarrow> ('b * LookupTableColumn list) set" where
"getLookupTables gLA x = 
  (\<lambda>a . (gate a, map snd (tableMap a))) ` gLA x
  "


class HasColumnVectorToBools =
  fixes getColumnVectorToBools :: 
    "'a \<Rightarrow> (RowIndex, Scalar option) Map \<Rightarrow> (RowIndex, bool) Map"

instantiation Polynomial_ext :: (type) HasColumnVectorToBools
begin
definition getColumnVectorToBools_Polynomial ::
  "Polynomial \<Rightarrow> (RowIndex, Scalar option) Map \<Rightarrow> (RowIndex, bool) Map" where
"getColumnVectorToBools_Polynomial _ m =
  map (\<lambda>(x, k). (x, k = Some 0)) m"
instance proof qed
end

instantiation Term :: HasColumnVectorToBools
begin
definition getColumnVectorToBools_Terms ::
  "Term \<Rightarrow> (RowIndex, Scalar option) Map \<Rightarrow> (RowIndex, bool) Map" where
"getColumnVectorToBools_Terms _ m = 
  map (\<lambda>(x, k). (x, k = Some 1)) m"
instance proof qed
end

(*
locale HasEvaluate =
  fixes evaluate :: "Argument \<Rightarrow> ('a, 'b) Map"
*)

fun getCellMap :: "Argument \<Rightarrow> (CellReference, Scalar) Map" where
"getCellMap arg = statement arg @ witness arg"

fun mapKeys ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'c) Map \<Rightarrow> ('b, 'c) Map" where
"mapKeys f = map (\<lambda>(x, y). (f x, y))"

fun mapMap ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) Map \<Rightarrow> ('c, 'b) Map" where
"mapMap f = map (\<lambda>(x, y). (x, f y))"

type_synonym ('a, 'b) HasEvaluate = "Argument \<Rightarrow> 'a \<rightharpoonup> 'b"

fun map_filterWithKey :: "
  ('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) Map \<Rightarrow> ('a, 'b) Map" where
"map_filterWithKey f = filter (f \<circ> fst)"

fun getEvaluate_PolynomialVariable_Map_RowIndex_Scalar ::
  "(PolynomialVariable, (RowIndex, Scalar) Map) HasEvaluate" where
"getEvaluate_PolynomialVariable_Map_RowIndex_Scalar arg v =
  Some
    (mapKeys rowIndex
      (filter (\<lambda>(k, _). colIndex k = colIndex v) 
            (getCellMap arg)))
"

fun getEvaluate_RowCount_PolynomialVariable_Map_RowIndex_Scalar :: "
  (RowCount * PolynomialVariable, (RowIndex, Scalar) Map) HasEvaluate" where
"getEvaluate_RowCount_PolynomialVariable_Map_RowIndex_Scalar arg (n, v) = 
  Some
    (mapKeys (\<lambda>k. (rowIndex v - rowIndex k) mod n)
      (filter (\<lambda>(k, _). colIndex k = colIndex v) 
            (getCellMap arg)))"

fun map_union_with :: "
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('k \<rightharpoonup> 'a) \<Rightarrow> 
  ('k \<rightharpoonup> 'a) \<Rightarrow> 
  ('k \<rightharpoonup> 'a)" where
"map_union_with f m1 m2 k =
  (case (m1 k, m2 k) of
    (None, r2) \<Rightarrow> r2 |
    (r1, None) \<Rightarrow> r1 |
    (Some r1, Some r2) \<Rightarrow> Some (f r1 r2)
  )
"

fun list_map_union_with :: "
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'a) Map" where
"list_map_union_with f m1 m2 = []
"

(*Multiplication should be swapped out for modular variant*)
fun getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar ::
  "(RowCount * PowerProduct * Coefficient, (RowIndex, Scalar) Map) HasEvaluate" where
"getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar arg (n, \<lparr> unPowerProduct = m \<rparr>, c) = 
  (let evaluate = getEvaluate_PolynomialVariable_Map_RowIndex_Scalar in
  (let lm :: (RowIndex, Scalar) Map list option = 
       those (map (\<lambda>(v, e). map_option (mapMap (\<lambda>d. d ^ nat e))  (evaluate arg v)) m) in
  (if m = []
   then Some (map (\<lambda>x. (of_nat x, c)) [0..<nat n])
   else map_option (\<lambda>l. mapMap (\<lambda>a. a * c) 
                               (foldr (list_map_union_with (*)) l [])) lm
  )))"

fun specM :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
"specM f l = those (map f l)"

(*Addition should be swapped out for modular variant*)
fun getEvaluate_RowCount_Polynomial_Map_RowIndex_Scalar ::
  "(RowCount * Polynomial, RowIndex \<rightharpoonup> Scalar) HasEvaluate" where
"getEvaluate_RowCount_Polynomial_Map_RowIndex_Scalar arg (rc, \<lparr> unPolynomial = monos \<rparr>) =
  (let evaluate = getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar in
  map_option (\<lambda>l . foldr (map_union_with (+)) l Map.empty)
      (specM (evaluate arg \<circ> (\<lambda>b . (rc, b))) monos)
  )"

fun getRowSet :: "
  RowCount \<Rightarrow>
  RowIndex set option \<Rightarrow>
  RowIndex set" where 
"getRowSet n None = {x. 0 \<le> x \<and> x < n}" |
"getRowSet n (Some x) = x"

definition getCellMapRows :: "
  RowIndex set \<Rightarrow>
  (CellReference \<rightharpoonup> Scalar) \<Rightarrow>
  RowIndex \<rightharpoonup> (ColumnIndex \<rightharpoonup> Scalar)" where
"getCellMapRows rows cellMap = 
  (\<lambda>ri.
    if ri \<in> rows 
    then Some (\<lambda>ci. cellMap \<lparr> colIndex = ci, rowIndex = ri \<rparr>)
    else None
  )"

(*Left-biased map intersection*)
definition map_intersection :: "
  ('a \<rightharpoonup> 'b) \<Rightarrow>
  ('a \<rightharpoonup> 'c) \<Rightarrow>
  ('a \<rightharpoonup> 'b)" where
"map_intersection f g x =
  (case (f x, g x) of
    (Some a, Some _) \<Rightarrow> Some a |
    (None, _) \<Rightarrow> None |
    (_, None) \<Rightarrow> None
  )"

fun columnListToCellMap :: "
  ((RowIndex \<rightharpoonup> Scalar) * LookupTableColumn) list \<Rightarrow>
  CellReference \<rightharpoonup> Scalar" where
"columnListToCellMap cols (\<lparr> colIndex = ci, rowIndex = ri \<rparr>) = 
  None"

(*
Map.fromList
    [ (CellReference ci ri, x)
      | (row, LookupTableColumn ci) <- cols,
        (ri, x) <- Map.toList row
    ]
*)

definition getColumnListRows :: "
  RowIndex set \<Rightarrow>
  ((RowIndex \<rightharpoonup> Scalar) * LookupTableColumn) list \<Rightarrow>
  RowIndex \<rightharpoonup> (ColumnIndex \<rightharpoonup> Scalar)" where
"getColumnListRows rows = getCellMapRows rows \<circ> columnListToCellMap"

(*
getColumnListRows ::
  Set (RowIndex 'Absolute) ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
getColumnListRows rows = getCellMapRows rows . columnListToCellMap
*)

find_consts "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a)"

definition getLookupResults :: "
  RowCount \<Rightarrow>
  RowIndex set option \<Rightarrow>
  (CellReference \<rightharpoonup> Scalar) \<Rightarrow>
  ((RowIndex \<rightharpoonup> Scalar) * LookupTableColumn) list \<Rightarrow>
  (CellReference \<rightharpoonup> Scalar) option" where
"getLookupResults rc mRowSet cellMap table = 
  (let rowSet = getRowSet rc mRowSet in
  (let allRows = getRowSet rc None in
  (let cellMapAllRows = getCellMapRows allRows cellMap in
  (let tableCols = map_of (map ((\<lambda>x. (x, ())) \<circ> snd) table) in
  (let cellMapTableRows = map_map (\<lambda>x. map_intersection x tableCols) cellMapAllRows in
  (let cellMapTableInverse = None in
  (let tableRows = None in
  None
  )))))))"

(*
getLookupResults ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Map CellReference Scalar ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Either (ErrorMessage ann) (Map CellReference Scalar)
getLookupResults ann rc mRowSet cellMap table = do
  let rowSet = getRowSet rc mRowSet
      allRows = getRowSet rc Nothing
      cellMapAllRows = getCellMapRows allRows cellMap
      tableCols = Map.fromList ((,()) . (^. #unLookupTableColumn) . snd <$> table)
      cellMapTableRows = (`Map.intersection` tableCols) <$> cellMapAllRows

      cellMapTableInverse = inverseMap cellMapTableRows
      tableRows = getColumnListRows rowSet table

  rowsToCellMap . Map.fromList
    <$> sequence
      [ do
          tableRow <-
            maybe
              (Left (ErrorMessage ann "input table row index missing"))
              pure
              (Map.lookup ri tableRows)
          when (Map.size tableRow /= length table) $
            trace
              ("table: " <> show table)
              (Left (ErrorMessage ann ("table row is wrong size; duplicate column index in lookup table, or missing value in input column vectors? " <> pack (show (snd <$> table, tableRow)))))
          case Map.lookup tableRow cellMapTableInverse of
            Just ri' ->
              case Map.lookup ri' cellMapAllRows of
                Just r -> pure (ri, r)
                Nothing ->
                  Left
                    ( ErrorMessage
                        ann
                        ("argument table row lookup failed: " <> pack (show ri'))
                    )
            Nothing ->
              pure (ri, mempty) -- returning an empty row will result in no cells for this row
        | ri <- Set.toList rowSet
      ]
*)

definition performLookups :: "
  (RowCount * 'a, RowIndex \<rightharpoonup> Scalar option) HasEvaluate \<Rightarrow>
  RowCount \<Rightarrow>
  Argument \<Rightarrow>
  ('a InputExpression * LookupTableColumn) list \<Rightarrow>
  LookupTableOutputColumn \<Rightarrow>
  (RowIndex \<rightharpoonup> Scalar option) option" where
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

fun getEvaluate_RowCount_Term_Map_RowIndex_Scalar ::
  "(RowCount * Term, RowIndex \<rightharpoonup> Scalar option) HasEvaluate" where
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, trm) =
  (case trm of
    Var v \<Rightarrow> map_option (map_map Some) (getEvaluate_PolynomialVariable_Map_RowIndex_Scalar arg v) | 
    Const i \<Rightarrow> Some (\<lambda>x . (if 0 \<le> x \<and> x < rc then Some (Some i) else None)) |
    Plus x y \<Rightarrow> 
      ( let recx = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, x) in
      ( let recy = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, y) in
        None
      )) |
    Times x y \<Rightarrow> 
      ( let recx = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, x) in
      ( let recy = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, y) in
        None
      )) |
    Max x y \<Rightarrow> 
      ( let recx = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, x) in
      ( let recy = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, y) in
        None
      )) |
    IndLess x y \<Rightarrow> 
      ( let recx = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, x) in
      ( let recy = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (rc, y) in
        None
      )) |
    Lookup is outCol \<Rightarrow> None
  )"


(*
instance HasEvaluate (RowCount, Term) (Map (RowIndex 'Absolute) (Maybe Scalar)) where
  evaluate ann arg = uncurry $ \rc@(RowCount n) ->
    let rec = evaluate ann arg . (rc,)
     in \case
          Plus x y -> Map.unionWith (liftA2 (Group.+)) <$> rec x <*> rec y
          Times x y -> Map.unionWith (liftA2 (Ring.* )) <$> rec x <*> rec y
          Max x y -> Map.unionWith (liftA2 max) <$> rec x <*> rec y
          IndLess x y -> Map.unionWith (liftA2 lessIndicator) <$> rec x <*> rec y
          l@(Lookup is outCol) ->
            mapLeft
              ( \(ErrorMessage ann' msg) ->
                  ErrorMessage ann' ("performLookups " <> pack (show l) <> ": " <> msg)
              )
              (performLookups ann rc arg is outCol)
*)






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