theory LogicCircuitTypes
  imports Main
begin

(*In OSL Scalar is Word64. This can be implemented (see "HOL-Word" library),
  but isn't a built in type. I don't think this matters much, but we'll see. *)
type_synonym Scalar = "nat"
type_synonym RowCount = "Scalar"
type_synonym ColumnIndex = "int"
datatype ColumnType = Fixed | Advice | Instance
type_synonym ColumnTypes = "ColumnIndex \<rightharpoonup> ColumnType"
type_synonym EqualityConstrainableColumns = "ColumnIndex set"
type_synonym Label = string
type_synonym 'a InputExpression = "'a"
type_synonym LookupTableColumn = ColumnIndex
record 'a LookupArgument =
  label :: Label
  gate :: 'a
  tableMap :: "('a InputExpression * LookupTableColumn) list"
type_synonym 'a LookupArguments = "('a LookupArgument) set"
(*Note: In OSL, RowIndex has a parameter which doesn't seem to do anything*)
type_synonym RowIndex = "int"
record CellReference = 
  colIndex :: ColumnIndex
  rowIndex :: RowIndex
type_synonym EqualityConstraint = "CellReference set"
type_synonym EqualityConstraints = "EqualityConstraint list"
type_synonym FixedColumn = "Scalar list"
type_synonym FixedValues = "ColumnIndex \<rightharpoonup> FixedColumn"

record ('a, 'b) Circuit =
  columnTypes :: ColumnTypes
  equalityConstrainableColumns :: EqualityConstrainableColumns
  gateConstraints :: 'a
  lookupArguments :: "'b LookupArguments"
  rowCount :: RowCount
  equalityConstraints :: EqualityConstraints
  fixedValues :: FixedValues

type_synonym PolynomialVariable = CellReference
(*
record PolynomialVariable =
  colIndex :: ColumnIndex
  rowIndex :: RowIndex 
*)

type_synonym LookupTableOutputColumn = LookupTableColumn
datatype Term =
  Var PolynomialVariable |
  Lookup
      "(Term InputExpression * LookupTableColumn) list"
      LookupTableOutputColumn |
  Const Scalar |
  Plus Term Term |
  Times Term Term |
  Max Term Term |
  IndLess Term Term

datatype AtomicLogicConstraint = 
  Equals Term Term |
  LessThan Term Term

datatype LogicConstraint =
  Atom AtomicLogicConstraint |
  Not LogicConstraint |
  And LogicConstraint LogicConstraint |
  Or LogicConstraint LogicConstraint |
  Iff LogicConstraint LogicConstraint |
  Top |
  Bottom

(*In OSL FixedBound is Word64. This can be implemented (see "HOL-Word" library),
  but isn't a built in type. I don't think this matters much, but we'll see. *)
type_synonym FixedBound = "nat"
record LogicConstraints =
  constraints :: "(Label * LogicConstraint) list"
  bounds :: "ColumnIndex \<rightharpoonup> FixedBound"

type_synonym LogicCircuit = "(LogicConstraints, Term) Circuit"


type_synonym Exponent = int
type_synonym Coefficient = Scalar
type_synonym PowerProduct = "PolynomialVariable \<rightharpoonup> Exponent"
type_synonym Polynomial = "PowerProduct \<rightharpoonup> Coefficient"
type_synonym PolynomialDegreeBound = int

record PolynomialConstraints = 
  constraints :: "Polynomial list"
  degreeBound :: PolynomialDegreeBound

record StepType = 
  gateConstraints :: PolynomialConstraints
  lookupArguments :: "Polynomial LookupArguments"
  fixedValues :: FixedValues

type_synonym StepTypeId = Scalar
type_synonym SubexpressionId = Scalar
type_synonym InputSubexpressionId = SubexpressionId
type_synonym OutputSubexpressionId = SubexpressionId
type_synonym ResultExpressionId = SubexpressionId

record SubexpressionLink = 
  stepType :: StepTypeId
  inputs :: "InputSubexpressionId list"
  outputSL :: OutputSubexpressionId

type_synonym CaseNumberColumnIndex = ColumnIndex
type_synonym StepTypeColumnIndex = ColumnIndex
type_synonym StepIndicatorColumnIndex = ColumnIndex
type_synonym InputColumnIndex = ColumnIndex
type_synonym OutputColumnIndex = ColumnIndex
type_synonym NumberOfCases = Scalar

record TraceType =
  columnTypes :: ColumnTypes
  equalityConstrainableColumns :: EqualityConstrainableColumns
  equalityConstraints :: EqualityConstraints
  stepTypes :: "StepTypeId \<rightharpoonup> StepType"
  subexpressions :: "SubexpressionId set"
  links :: "SubexpressionLink set"
  results :: "ResultExpressionId set"
  caseNumberColumnIndex :: CaseNumberColumnIndex
  stepTypeColumnIndex :: StepTypeColumnIndex
  stepIndicatorColumnIndex :: StepIndicatorColumnIndex
  inputColumnIndices :: "InputColumnIndex list"
  outputColumnIndex :: OutputColumnIndex
  numCases :: NumberOfCases
  rowCount :: RowCount



end