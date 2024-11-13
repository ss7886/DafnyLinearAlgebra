include "matrix.dfy"

type MatrixRow = row : (Matrix, int) | 0 <= row.1 < matNumRows (row.0) witness *
type MatrixCol = col : (Matrix, int) | 0 <= col.1 < matNumCols (col.0) witness *

datatype Vector = 
    VectorInd (list : seq<real>)  // Defined inductively
    | MatrixRow (matRow : MatrixRow)  // Static (can't append values to a row)
    | MatrixCol (matCol : MatrixCol)  // Static (can't append values to a column)

const vecEmpty := VectorInd ([])

// Return the i-th row of a matrix as a vector
function matGetRow (mat : Matrix, i : int) : (res : Vector)
requires 0 <= i < matNumRows (mat)
ensures vecLength (res) == matNumCols (mat)
{
    Vector.MatrixRow ((mat, i))
}

// Return the i-th column of a matrix as a vector
function matGetCol (mat : Matrix, i : int) : (res : Vector)
requires 0 <= i < matNumCols (mat)
ensures vecLength (res) == matNumRows (mat)
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

predicate vecZero (vec : Vector)
{
    forall i | 0 <= i < vecLength (vec) :: vecGet (vec, i) == 0.0
}

// Append a value to an inductively defined vector and return the result
// Cannot append a value to a row or column of a matrix.
function vecAppend (x : real, vec : Vector) : (res : Vector)
ensures vecLength (res) == vecLength (vec) + 1
ensures res.VectorInd?
requires vec.VectorInd?
{
    VectorInd ([x] + vec.list)
}
