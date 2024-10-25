include "matrix.dfy"

type MatrixRow = matIndex : (Matrix, int) | 0 <= matIndex.1 < matNumRows (matIndex.0) witness *
type MatrixCol = matIndex : (Matrix, int) | 0 <= matIndex.1 < matNumCols (matIndex.0) witness *

datatype Vector = 
    VectorInd (vec : seq<real>)
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
reads *
requires 0 <= i < vecLength (vec)
{
    match vec
    case VectorInd (vec) => vec[i]
    case MatrixRow (matRow) => matGet (matRow.0, matRow.1, i)
    case MatrixCol (matCol) => matGet (matCol.0, i, matCol.1)
}

function vecAppend (x : real, vec : Vector) : (res : Vector)
reads *
ensures vecLength (res) == vecLength (vec) + 1
// ensures forall i | 0 <= i < vecLength (vec) :: vecGet (vec, i) == vecGet (res, i + 1)
ensures res.VectorInd?
requires vec.VectorInd?
{
    VectorInd ([x] + vec.vec)
}

predicate vecEquals (vec1 : Vector, vec2 : Vector)
reads *
requires vecLength (vec1) == vecLength (vec2)
{
    forall i | 0 <= i < vecLength (vec1) :: vecGet (vec1, i) == vecGet (vec2, i)
}

lemma vecEqualsSymmetric (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (vec1, vec2) <==> vecEquals (vec2, vec1)
{}

lemma vecEqualsTransitive (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2) && vecEquals (vec2, vec3)
ensures vecEquals (vec1, vec3)
{}

lemma vecEqualsAppend (vec1 : Vector, vec2 : Vector, x : real)
requires vecLength (vec1) == vecLength (vec2)
requires vecEquals (vec1, vec2)
requires vec1.VectorInd? && vec2.VectorInd?
ensures vecEquals (vecAppend (x, vec1), vecAppend (x, vec2))
{
    assert vecGet (vecAppend (x, vec1), 0) == x;
    assert vecGet (vecAppend (x, vec2), 0) == x;
    assert forall i {:trigger vecGet (vecAppend (x, vec1), i)} | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (vecAppend (x, vec1), i) == vecGet (vec1, i - 1);
    assert forall i {:trigger vecGet (vecAppend (x, vec1), i)} | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (vecAppend (x, vec2), i) == vecGet (vec2, i - 1);
    assert forall i {:trigger vecGet (vecAppend (x, vec1), i + 1)} | 1 <= i < vecLength (vec1) + 1 :: 
            vecGet (vecAppend (x, vec1), i) == vecGet (vecAppend (x, vec2), i);
    assert forall i | 0 <= i < vecLength (vec1) + 1 :: vecGet (vecAppend (x, vec1), i) == vecGet (vecAppend (x, vec2), i);
}