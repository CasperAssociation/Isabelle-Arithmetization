theory LogicCircuitTypes_Map
  imports Main
begin

type_synonym ('a, 'b) Map = "('a * 'b) list"

(*In OSL Scalar is Word64. It's supposed to represent a finite field, specifically
  the Goldilocks of size (2^64-2^32)+1. *)
type_synonym Scalar = "int"
definition GoldilocksSize :: int where
  [simp]:"GoldilocksSize = (2^64-2^32)+1"
type_synonym RowCount = "Scalar"
type_synonym ColumnIndex = "int"
datatype ColumnType = Fixed | Advice | Instance
type_synonym ColumnTypes = "(ColumnIndex, ColumnType) Map"
type_synonym EqualityConstrainableColumns = "ColumnIndex set"
type_synonym Label = string
type_synonym 'a InputExpression = "'a"
type_synonym LookupTableColumn = ColumnIndex
record 'a LookupArgument =
  label :: Label
  gate :: 'a
  tableMap :: "('a InputExpression, LookupTableColumn) Map"
type_synonym 'a LookupArguments = "('a LookupArgument) set"
(*Note: In OSL, RowIndex has a parameter which doesn't seem to do anything*)
type_synonym RowIndex = "int"
record CellReference = 
  colIndex :: ColumnIndex
  rowIndex :: RowIndex
type_synonym EqualityConstraint = "CellReference set"
type_synonym EqualityConstraints = "EqualityConstraint list"
type_synonym FixedColumn = "Scalar list"
type_synonym FixedValues = "(ColumnIndex, FixedColumn) Map"

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
      "(Term InputExpression, LookupTableColumn) Map"
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

(*In OSL FixedBound is Word64. It's sipposed to represent
   an absolute value bound on a given column *)
type_synonym FixedBound = "nat"
record LogicConstraints =
  constraints :: "(Label, LogicConstraint) Map"
  bounds :: "(ColumnIndex, FixedBound) Map"

type_synonym LogicCircuit = "(LogicConstraints, Term) Circuit"


type_synonym Exponent = int
type_synonym Coefficient = Scalar
record PowerProduct = 
  unPowerProduct :: "(PolynomialVariable, Exponent) Map"

record Polynomial = 
  unPolynomial :: "(PowerProduct, Coefficient) Map"
type_synonym PolynomialDegreeBound = int

record PolynomialConstraints = 
  constraints :: "(Label, Polynomial) Map"
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
  stepTypes :: "(StepTypeId, StepType) Map"
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



type_synonym InputMatrix = "(ColumnIndex, FixedColumn) Map"

type_synonym Statement = "(CellReference, Scalar) Map"
type_synonym Witness = "(CellReference, Scalar) Map"
record Argument =
  statement :: Statement
  witness :: Witness


end
