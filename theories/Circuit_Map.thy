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
    "'a \<Rightarrow> (Absolute RowIndex, Scalar option) Map \<Rightarrow> (Absolute RowIndex, bool) Map"

instantiation Polynomial_ext :: (type) HasColumnVectorToBools
begin
definition getColumnVectorToBools_Polynomial ::
  "Polynomial \<Rightarrow> (Absolute RowIndex, Scalar option) Map \<Rightarrow> (Absolute RowIndex, bool) Map" where
"getColumnVectorToBools_Polynomial _ m =
  map (\<lambda>(x, k). (x, k = Some 0)) m"
instance proof qed
end

instantiation Term :: HasColumnVectorToBools
begin
definition getColumnVectorToBools_Terms ::
  "Term \<Rightarrow> (Absolute RowIndex, Scalar option) Map \<Rightarrow> (Absolute RowIndex, bool) Map" where
"getColumnVectorToBools_Terms _ m = 
  map (\<lambda>(x, k). (x, k = Some 1)) m"
instance proof qed
end

(*
locale HasEvaluate =
  fixes evaluate :: "Argument \<Rightarrow> ('a, 'b) Map"
*)

fun getCellMap :: "Argument \<Rightarrow> (Absolute CellReference, Scalar) Map" where
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
  "(PolynomialVariable, (Absolute RowIndex, Scalar) Map) HasEvaluate" where
"getEvaluate_PolynomialVariable_Map_RowIndex_Scalar arg v =
  Some
    (mapKeys rowIndex
      (filter (\<lambda>(k, _). colIndex k = colIndex v) 
            (getCellMap arg)))
"

fun getEvaluate_RowCount_PolynomialVariable_Map_RowIndex_Scalar :: "
  (RowCount * PolynomialVariable, (Absolute RowIndex, Scalar) Map) HasEvaluate" where
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

fun combineVals :: "
  'k \<Rightarrow>
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  'a" where
"combineVals k f m1 m2 =
  (case (map_of m1 k, map_of m2 k) of 
    (Some x, None) \<Rightarrow> x |
    (None, Some x) \<Rightarrow> x |
    (Some x, Some y) \<Rightarrow> f x y
  )"

fun list_map_union_with :: "
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'a) Map" where
"list_map_union_with f m1 m2 = 
  (let keys = remdups (map fst m1 @ map fst m2) in
   map (\<lambda>k. (k, combineVals k f m1 m2)) keys
  )
"

value "list_map_union_with (\<lambda>x y. (x @ y)) 
          [(5 :: nat, ''a''), (3, ''b'')] 
          [(5, ''A''), (7, ''C'')]"

fun intersectVals :: "
  'k \<Rightarrow>
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'b) Map \<Rightarrow> 
  'a list" where
"intersectVals k m1 m2 =
  (case (map_of m1 k, map_of m2 k) of 
    (x, None) \<Rightarrow> [] |
    (None, x) \<Rightarrow> [] |
    (Some x, Some y) \<Rightarrow> [x]
  )"

fun list_map_intersection :: "
  ('k, 'a) Map \<Rightarrow> 
  ('k, 'b) Map \<Rightarrow> 
  ('k, 'a) Map" where
"list_map_intersection m1 m2 = 
  (let keys = remdups (map fst m1 @ map fst m2) in
   concat (map (\<lambda>k. map (\<lambda>x. (k, x)) (intersectVals k m1 m2)) keys)
  )
"

value "list_map_intersection [(5 :: nat, a), (3, b)] [(5, A), (7, C)]"

(*Multiplication should be swapped out for modular variant*)
fun getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar ::
  "(RowCount * PowerProduct * Coefficient, (Absolute RowIndex, Scalar) Map) HasEvaluate" where
"getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar arg (n, \<lparr> unPowerProduct = m \<rparr>, c) = 
  (let evaluate = getEvaluate_PolynomialVariable_Map_RowIndex_Scalar in
  (let lm :: (Absolute RowIndex, Scalar) Map list option = 
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
  "(RowCount * Polynomial, (Absolute RowIndex, Scalar option) Map) HasEvaluate" where
"getEvaluate_RowCount_Polynomial_Map_RowIndex_Scalar arg (rc, \<lparr> unPolynomial = monos \<rparr>) =
  (let evaluate = getEvaluate_RowCount_PowerProduct_Coefficient_Map_RowIndex_Scalar in
  map_option (\<lambda>l . mapMap Some (foldr (list_map_union_with (+)) l []))
      (specM (evaluate arg \<circ> (\<lambda>b . (rc, b))) monos)
  )"


fun lessIndicator :: "Scalar \<Rightarrow> Scalar \<Rightarrow> Scalar" where
"lessIndicator x y = (if x < y then 1 else 0)"

fun getRowSet :: "
  RowCount \<Rightarrow>
  Absolute RowIndex set option \<Rightarrow>
  Absolute RowIndex set" where
"(getRowSet n None) = of_nat ` set (upt 0 (nat n))" |
"(getRowSet n (Some x)) = x"

fun getRowList :: "
  RowCount \<Rightarrow>
  Absolute RowIndex list option \<Rightarrow>
  Absolute RowIndex list" where
"(getRowList n None) = map of_nat (upt 0 (nat n))" |
"(getRowList n (Some x)) = x"

fun list_map_unions_with :: "
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
  ('k, 'a) Map list \<Rightarrow>
  ('k, 'a) Map" where
"list_map_unions_with f ms = foldr (list_map_union_with f) ms []"

fun getCellMapRows :: "
  (Absolute RowIndex) set \<Rightarrow>
  (Absolute CellReference, Scalar) Map \<Rightarrow>
  (Absolute RowIndex, (ColumnIndex, Scalar) Map) Map" where
"getCellMapRows rows cellMap = 
  list_map_unions_with (@) 
    (map (\<lambda>(cr, x). [(rowIndex cr, [(colIndex cr, x)])])
         (filter (\<lambda>(cr, x). rowIndex cr \<in> rows) cellMap))"

fun columnListToCellMap :: "
  ((Absolute RowIndex, Scalar) Map * LookupTableColumn) list \<Rightarrow>
  (Absolute CellReference, Scalar) Map" where
"columnListToCellMap cols = 
  List.bind cols (\<lambda>(row, ci).
  List.bind row (\<lambda>(ri, x).
    [(\<lparr>colIndex=ci, rowIndex = ri\<rparr>, x)]
  ))"

fun getColumnListRows :: "
  (Absolute RowIndex) set \<Rightarrow>
  ((Absolute RowIndex, Scalar) Map * LookupTableColumn) list \<Rightarrow>
  (Absolute RowIndex, (ColumnIndex, Scalar) Map) Map" where
"getColumnListRows rows = getCellMapRows rows \<circ> columnListToCellMap"

fun rowsToCellMap :: "
  (Absolute RowIndex, (ColumnIndex, Scalar) Map) Map \<Rightarrow>
  (Absolute CellReference, Scalar) Map" where
"rowsToCellMap rows =
  List.bind rows (\<lambda>(ri, cols).
  List.bind cols (\<lambda>(ci, x).
    [(\<lparr>colIndex=ci, rowIndex=ri\<rparr>, x)]
  ))"

fun map_size :: "('a, 'b) Map \<Rightarrow> nat" where
"map_size m = (length \<circ> remdups \<circ> map fst) m"

fun getLookupResults :: "
  RowCount \<Rightarrow>
  Absolute RowIndex list option \<Rightarrow>
  (Absolute CellReference, Scalar) Map \<Rightarrow>
  ((Absolute RowIndex, Scalar) Map * LookupTableColumn) list \<Rightarrow>
  (Absolute CellReference, Scalar) Map option" where
"getLookupResults rc mRowSet cellMap inputTable = 
  (let rowSet = getRowList rc mRowSet in
  (let allRows = getRowSet rc None in
  (let cellMapAllRows :: (Absolute RowIndex, (ColumnIndex, Scalar) Map) Map
        = getCellMapRows allRows cellMap in
  (let tableCols :: (ColumnIndex, unit) Map= 
        map ((\<lambda>x. (x, ())) \<circ> snd) inputTable in
  (let cellMapTableRows :: (Absolute RowIndex , (ColumnIndex, Scalar) Map) Map
        = mapMap (\<lambda>x. list_map_intersection x tableCols) cellMapAllRows in
  (let cellMapTableInverse = map (\<lambda>(x, y). (y, x)) cellMapTableRows in
  (let tableRows = getColumnListRows (set rowSet) inputTable in
  map_option rowsToCellMap (those (map (\<lambda>ri. 
    Option.bind (map_of tableRows ri) (\<lambda>inputTableRow. (
    if (map_size inputTableRow \<noteq> length inputTable) then None
    else (case map_of cellMapTableInverse inputTableRow of
      None \<Rightarrow> Some (ri, []) |
      Some ri' \<Rightarrow> (
        case map_of cellMapAllRows ri' of
          None \<Rightarrow> None |
          Some r \<Rightarrow> Some (ri, r)
    ))))
  ) rowSet)))))))))"

(*Note that this case is different from the haskell implementation
  in that part of `performLookups` is computed in getEvaluate_RowCount_Term_Map_RowIndex_Scalar.
  Specifically, is is split up and its first part is partially evaluated there.
  This is necessary for termination checking. *)
fun performLookups :: "
  RowCount \<Rightarrow>
  Argument \<Rightarrow>
  (Absolute RowIndex, Scalar option) Map list option \<Rightarrow>
  LookupTableColumn list \<Rightarrow>
  LookupTableOutputColumn \<Rightarrow>
  ((Absolute RowIndex, Scalar option) Map) option" where
"performLookups rc arg is1 is2 c = 
  Option.bind (map_option (map (map (\<lambda>(x, y). (x, option.the y)))) is1) 
  (\<lambda>inputTable.
  Option.bind (getLookupResults rc None (getCellMap arg) (zip inputTable is2))
  (\<lambda>results.
  (let allRows = getRowList rc None in
  (let results' = mapMap Some (mapKeys rowIndex (map_filterWithKey (\<lambda>k. colIndex k = c) results)) in
  Some (results' @ map (\<lambda>k. (k, None)) allRows)
  ))))"


fun getEvaluate_RowCount_Term_Map_RowIndex_Scalar ::
  "(RowCount * Term, (Absolute RowIndex, Scalar option) Map) HasEvaluate" where
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Var v) =
   map_option (mapMap Some) (getEvaluate_RowCount_PolynomialVariable_Map_RowIndex_Scalar arg (n, v))" |
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Const i) =
   Some (map (\<lambda>x. (of_nat x, Some i)) (upt 0 (nat n)))" |
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Plus x y) =
  (let recx :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, x) in
  (let recy :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, y) in
    combine_options (list_map_union_with (combine_options (+))) recx recy
  ))" |
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Times x y) =
  (let recx :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, x) in
  (let recy :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, y) in
    combine_options (list_map_union_with (combine_options (*))) recx recy
  ))" |
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Max x y) =
  (let recx :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, x) in
  (let recy :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, y) in
    combine_options (list_map_union_with (combine_options max)) recx recy
  ))" |
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, IndLess x y) =
  (let recx :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, x) in
  (let recy :: ((Absolute RowIndex, Scalar option) Map) option = getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, y) in
    combine_options (list_map_union_with (combine_options lessIndicator)) recx recy
  ))" |
(*Note that this case is different from the haskell implementation
  in that part of `performLookups` is computed here. This is
  necessary for termination checking.*)
"getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, Lookup is outCol) =
  (let is1 :: (Absolute RowIndex, Scalar option) Map list option =
       those (map (\<lambda>x. getEvaluate_RowCount_Term_Map_RowIndex_Scalar arg (n, fst x)) is) in
  (let is2 = map snd is in
  performLookups n arg is1 is2 outCol
  ))"




end