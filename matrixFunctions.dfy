include "vector.dfy"

predicate matEquals (mat1 : Matrix, mat2 : Matrix)
requires matNumRows (mat1) == matNumRows (mat2)
requires matNumCols (mat1) == matNumCols (mat2)
{
    forall i | 0 <= i < matNumRows (mat1) :: vecEquals (matGetRow (mat1, i), matGetRow (mat2, i))
}

predicate matIsIdentity (mat : Matrix)
requires matNumRows (mat) == matNumCols (mat)
{
    forall i, j | 0 <= i < matNumRows (mat) && 0 <= j < matNumRows (mat) ::
        if i == j then matGet (mat, i, j) == 1.0 else matGet (mat, i, j) == 0.0 
}

predicate matIsTranspose (mat1 : Matrix, mat2 : Matrix)
requires matNumRows (mat1) == matNumCols (mat2)
requires matNumCols (mat1) == matNumRows (mat2)
{
    forall i, j | 0 <= i < matNumRows (mat1) && 0 <= j < matNumCols (mat1) ::
        matGet (mat1, i, j) == matGet (mat2, j, i)
}

predicate matIsSymmetric (mat : Matrix)
requires matNumRows (mat) == matNumCols (mat)
{
    matIsTranspose (mat, mat)
}

function matEmpty (numCols : int) : Matrix
requires 0 <= numCols
{
    ([], 0, numCols)
}

function matAppendRow (row : Vector, mat : Matrix) : (res : Matrix)
requires vecLength (row) == matNumCols (mat)
requires row.VectorInd?
ensures matNumCols (res) == matNumCols (mat)
ensures matNumRows (res) == matNumRows (mat) + 1
ensures forall i | 0 <= i < vecLength (row) ::
        matGet (res, 0, i) == vecGet (row, i)
ensures forall i, j | 0 <= i < matNumRows (mat) && 0 <= j < matNumCols (mat) ::
        matGet (mat, i, j) == matGet (res, i + 1, j)
{
    ([row.list] + mat.0, mat.1 + 1, mat.2)
}

function makeMatrix (rows : int, cols : int, f : (int, int) --> real) : (res : Matrix)
requires 0 <= rows
requires 0 <= cols
requires forall i, j | 0 <= i < rows && 0 <= j < cols :: f.requires(i, j)
ensures matNumRows (res) == rows
ensures matNumCols (res) == cols
ensures forall i, j | 0 <= i < rows && 0 <= j < cols :: matGet (res, i, j) == f (i, j) 
{
    makeMatrixAuxRows (rows, cols, f, 0)
}

function makeMatrixAuxRows (rows : int, cols : int, f : (int, int) --> real, i : int) : (res : Matrix)
requires 0 <= rows
requires 0 <= cols
requires 0 <= i <= rows
requires forall m, n | 0 <= m < rows && 0 <= n < cols :: f.requires(m, n)
ensures matNumRows (res) == rows - i
ensures matNumCols (res) == cols
ensures forall m, n | i <= m < rows && 0 <= n < cols :: matGet (res, m - i, n) == f (m, n)
decreases rows - i
{
    if i == rows
    then matEmpty (cols)
    else matAppendRow (makeMatrixRow (rows, cols, f, i, 0), makeMatrixAuxRows (rows, cols, f, i + 1))
}

function makeMatrixRow (rows : int, cols : int, f : (int, int) --> real, i : int, j : int) : (res : Vector)
requires 0 <= rows
requires 0 <= cols
requires 0 <= i < rows
requires 0 <= j <= cols
requires forall m, n | 0 <= m < rows && 0 <= n < cols :: f.requires(m, n)
ensures vecLength (res) == cols - j
ensures forall k | j <= k < cols :: vecGet (res, k - j) == f (i, k)
decreases cols - j
{
    if j == cols
    then vecEmpty
    else vecAppend (f (i, j), makeMatrixRow (rows, cols, f, i, j + 1))
}

function matTr (mat : Matrix) : (res : Matrix)
ensures matNumRows (mat) == matNumCols (res)
ensures matNumCols (mat) == matNumRows (res)
ensures matIsTranspose (mat, res)
{
    var f := (i, j) requires 0 <= i < matNumCols (mat) && 0 <= j < matNumRows (mat) => matGet(mat, j, i);
    makeMatrix (matNumCols (mat), matNumRows (mat), f)
}
