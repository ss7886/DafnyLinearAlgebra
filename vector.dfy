include "matrix.dfy"

type MatrixRow = row : (Matrix, int) | 0 <= row.1 < matNumRows (row.0) witness *
type MatrixCol = col : (Matrix, int) | 0 <= col.1 < matNumCols (col.0) witness *

datatype Vector = 
    VectorInd (list : seq<real>)  // Defined inductively
    | MatrixRow (matRow : MatrixRow)
    | MatrixCol (matCol : MatrixCol)

const vecEmpty := VectorInd ([])

function matGetRow (mat : Matrix, i : int) : Vector
requires 0 <= i < matNumRows (mat)
{
    Vector.MatrixRow ((mat, i))
}

function matGetCol (mat : Matrix, i : int) : Vector
requires 0 <= i < matNumCols (mat)
{
    Vector.MatrixCol ((mat, i))
}

function vecLength (vec : Vector) : int
ensures 0 <= vecLength(vec)
{
    match vec
    case VectorInd (vec) => |vec|
    case MatrixRow (matRow) => matNumCols (matRow.0)
    case MatrixCol (matCol) => matNumRows (matCol.0)
}

function vecGet (vec : Vector, i : int) : real
requires 0 <= i < vecLength (vec)
{
    match vec
    case VectorInd (vec) => vec[i]
    case MatrixRow (matRow) => matGet (matRow.0, matRow.1, i)
    case MatrixCol (matCol) => matGet (matCol.0, i, matCol.1)
}

predicate vecEquals (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
{
    forall i | 0 <= i < vecLength (vec1) :: vecGet (vec1, i) == vecGet (vec2, i)
}

function vecAppend (x : real, vec : Vector) : (res : Vector)
ensures vecLength (res) == vecLength (vec) + 1
// ensures forall i | 0 <= i < vecLength (vec) :: vecGet (vec, i) == vecGet (res, i + 1)
ensures res.VectorInd?
requires vec.VectorInd?
{
    VectorInd ([x] + vec.list)
}
