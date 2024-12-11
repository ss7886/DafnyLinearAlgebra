include "vector.dfy"

// Returns the inner product of two vectors
function vecDotProd (vec1 : Vector, vec2 : Vector) : real
requires vecLength (vec1) == vecLength (vec2)
{
    vecDotProdAux (vec1, vec2, 0)
}

function vecDotProdAux (vec1 : Vector, vec2 : Vector, i : int) : real
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
decreases vecLength (vec1) - i
{
    if i == vecLength (vec1)
    then 0.0
    else vecGet (vec1, i) * vecGet (vec2, i) + vecDotProdAux (vec1, vec2, i + 1)
}

// Returns the squared euclidean norm (2-norm) of a vector
function vecNormSq(vec : Vector) : real
{
    vecDotProd (vec, vec)
}

// Returns the sum of two vectors
function vecAdd (vec1 : Vector, vec2 : Vector) : (res : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecLength (res) == vecLength (vec1)
ensures forall i | 0 <= i < vecLength (res) :: vecGet (res, i) == vecGet (vec1, i) + vecGet (vec2, i)
{
    vecAddAux (vec1, vec2, 0)
}

function vecAddAux (vec1 : Vector, vec2 : Vector, i : int) : (res : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecLength (res) == vecLength (vec1) - i
ensures forall j | i <= j < vecLength(vec1) :: vecGet (res, j - i) == vecGet (vec1, j) + vecGet (vec2, j)
decreases vecLength (vec1) - i
{
    if i == vecLength (vec1)
    then vecEmpty
    else vecAppend (vecGet (vec1, i) + vecGet (vec2, i), vecAddAux (vec1, vec2, i + 1))
}

// Returns the product of a vector with a scalar
function vecScale (alpha : real, vec : Vector) : (res : Vector)
ensures vecLength (res) == vecLength (vec)
ensures forall i | 0 <= i < vecLength (vec) :: vecGet (res, i) == alpha * vecGet (vec, i)
{
    vecScaleAux (alpha, vec, 0)
}

function vecScaleAux (alpha : real, vec : Vector, i : int) : (res : Vector)
requires 0 <= i <= vecLength (vec)
ensures vecLength (res) == vecLength (vec) - i
ensures forall j | i <= j < vecLength (vec) :: vecGet (res, j - i) == alpha * vecGet (vec, j)
decreases vecLength (vec) - i
{
    if i == vecLength (vec)
    then vecEmpty
    else vecAppend (alpha * vecGet (vec, i), vecScaleAux (alpha, vec, i + 1))
}

// Returns the difference between two vectors
function vecSub (vec1 : Vector, vec2 : Vector) : (res : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecLength (res) == vecLength (vec1)
ensures forall i | 0 <= i < vecLength (res) :: vecGet (res, i) == vecGet (vec1, i) - vecGet (vec2, i)
{
    vecAdd (vec1, vecScale (-1.0, vec2))
}
