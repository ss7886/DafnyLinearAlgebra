include "vectorFunctions.dfy"
include "matrixFunctions.dfy"

// Returns the product of matrix-vector multiplication
function matVecMult (mat : Matrix, vec : Vector) : (res : Vector)
requires matNumCols (mat) == vecLength (vec)
ensures vecLength (res) == matNumRows (mat)
ensures forall i | 0 <= i < matNumRows (mat) :: vecGet (res, i) == vecDotProd (matGetRow (mat, i), vec)
{
    matVecMultAux (mat, vec, 0)
}

function matVecMultAux (mat : Matrix, vec : Vector, i : int) : (res : Vector)
requires matNumCols (mat) == vecLength (vec)
requires 0 <= i <= matNumRows (mat)
ensures vecLength (res) == matNumRows (mat) - i
ensures forall j | i <= j < matNumRows (mat) :: vecGet (res, j - i) == vecDotProd (matGetRow (mat, j), vec)
decreases matNumRows (mat) - i
{
    if i == matNumRows (mat) 
    then vecEmpty
    else
        var row := matGetRow (mat, i);
        vecAppend (vecDotProd (row, vec), matVecMultAux (mat, vec, i + 1))
}

// Returns the product of matrix-matrix multiplication
function matMatMult (mat1 : Matrix, mat2 : Matrix) : (res : Matrix)
requires matNumCols (mat1) == matNumRows (mat2)
ensures matNumRows (mat1) == matNumRows (res)
ensures matNumCols (mat2) == matNumCols (res)
ensures forall i, j | 0 <= i < matNumRows (res) && 0 <= j < matNumCols (res) ::
    matGet (res, i, j) == vecDotProd (matGetRow (mat1, i), matGetCol (mat2, j))
{
    var f := (i : int, j : int)
        requires 0 <= i < matNumRows (mat1) && 0 <= j < matNumCols (mat2) =>
        vecDotProd (matGetRow (mat1, i), matGetCol (mat2, j));
    makeMatrix (matNumRows (mat1), matNumCols (mat2), f)
}

// Checks whether two square matrices are inverses of each other
predicate matIsInverse (mat1 : Matrix, mat2 : Matrix)
requires matNumRows (mat1) == matNumCols (mat1)
requires matNumRows (mat2) == matNumCols (mat2)
requires matNumRows (mat1) == matNumRows (mat2)
{
    matIsIdentity (matMatMult (mat1, mat2)) && matIsIdentity (matMatMult (mat2, mat1))
}
