include "../vectorFunctions.dfy"

// x + y = y + x
lemma vecAddSymmetric (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (vecAdd (vec1, vec2), vecAdd (vec2, vec1))
{}

// (x + y) + z = x + (y + z)
lemma vecAddTransitive (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecEquals (vecAdd (vecAdd (vec1, vec2), vec3), vecAdd (vec1, vecAdd (vec2, vec3)))
{}

// <v1, v2> = <v2, v1>
lemma vecDotProdSymm (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vec1, vec2) == vecDotProd (vec2, vec1)
{
    vecDotProdAuxSymm (vec1, vec2, 0);
}

lemma vecDotProdAuxSymm (vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec2, i) == vecDotProdAux (vec2, vec1, i)
decreases vecLength (vec1) - i
{}

// v1 == v2 => <v1, v3> = <v2, v3>
lemma vecDotProdEq (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2)
ensures vecDotProd (vec1, vec3) == vecDotProd (vec2, vec3)
{
    vecDotProdAuxEq (vec1, vec2, vec3, 0);
}

lemma vecDotProdAuxEq (vec1 : Vector, vec2 : Vector, vec3 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec3, i) == vecDotProdAux (vec2, vec3, i)
decreases vecLength (vec1) - i
{}

lemma vecDotProdScale (alpha : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vecScale (alpha, vec1), vec2) == alpha * vecDotProd (vec1, vec2)
{
    vecDotProdAuxScale (alpha, vec1, vec2, 0);
}

lemma vecDotProdAuxScale (alpha : real, vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vecScale (alpha, vec1), vec2, i) == alpha * vecDotProdAux (vec1, vec2, i)
decreases vecLength (vec1) - i
{}

lemma vecDotProdAuxDist (vec1 : Vector, vec2 : Vector, vec3 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vecAdd (vec2, vec3), i) == 
    vecDotProdAux (vec1, vec2, i) + vecDotProdAux (vec1, vec3, i)
decreases vecLength (vec1) - i
{}

// <x, y + z> = <x, y> + <x, z>
lemma vecDotProdDistRH (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecDotProd (vec1, vecAdd (vec2, vec3)) == vecDotProd (vec1, vec2) + vecDotProd (vec1, vec3)
{
    vecDotProdAuxDist (vec1, vec2, vec3, 0);
}

// <x + y, z> = <x, z> + <y, z>
lemma vecDotProdDistLH (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecDotProd (vecAdd (vec1, vec2), vec3) == vecDotProd (vec1, vec3) + vecDotProd (vec2, vec3)
{
    vecDotProdSymm (vecAdd (vec1, vec2), vec3);
    vecDotProdDistRH (vec3, vec1, vec2);
    vecDotProdSymm (vec3, vec1);
    vecDotProdSymm (vec3, vec2);
}

// <x + y, w + z> = <x, w> + <x, z> + <y, w> + <y, z>
lemma vecDotProdDist2 (vec1 : Vector, vec2 : Vector, vec3 : Vector, vec4 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecLength (vec1) == vecLength (vec4)
ensures vecDotProd (vecAdd (vec1, vec2), vecAdd (vec3, vec4)) == 
        vecDotProd (vec1, vec3) + vecDotProd (vec1, vec4) + vecDotProd (vec2, vec3) + vecDotProd (vec2, vec4)
{
    // <v1 + v2, v3 + v4>
    vecDotProdDistRH (vecAdd (vec1, vec2), vec3, vec4);
    // <v1 + v2, v3 + v4> = <v1 + v2, v3> + <v1 + v2, v4>
    vecDotProdDistLH (vec1, vec2, vec3);
    vecDotProdDistLH (vec1, vec2, vec4);
    // <v1 + v2, v3> + <v1 + v2, v4> = <v1, v3> + <v2, v3> + <v1, v4> + <v2, v4>
}

// ||v1 + v2||^2 = ||v1||^2 + 2 <v1, v2> + ||v2||^2
lemma vecNormDist (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecNormSq (vecAdd (vec1, vec2)) == vecNormSq (vec1) + 2.0 * vecDotProd (vec1, vec2) + vecNormSq (vec2)
{
    // ||v1 + v2|| = <v1 + v2, v1 + v2>
    vecDotProdDist2 (vec1, vec2, vec1, vec2);
    // <v1 + v2, v1 + v2> = <v1, v1> + <v1, v2> + <v2, v1> + <v2, v2> 
    vecDotProdSymm (vec2, vec1);
    // <v1, v1> + <v1, v2> + <v2, v1> + <v2, v2> = <v1, v1> + 2 <v1, v2> + <v2, v2>
}

// (x1 :: vec1) + (x2 :: vec2) == (x1 + x2 :: vec1 + vec2)
lemma vecAppendDist (x1 : real, x2 : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vec1.VectorInd? && vec2.VectorInd?
ensures vecEquals (vecAdd (vecAppend (x1, vec1), vecAppend (x2, vec2)), vecAppend (x1 + x2, vecAdd (vec1, vec2)))
{
    var res1 := vecAdd (vecAppend (x1, vec1), vecAppend (x2, vec2));
    var res2 := vecAppend (x1 + x2, vecAdd (vec1, vec2));
    assert forall i | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (res1, i) == 
            vecGet (vec1, i - 1) + vecGet (vec2, i - 1);    
}

lemma vecDotProdZero (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecZero (vec2)
ensures vecDotProd (vec1, vec2) == 0.0
{
    vecDotProdZeroAux (vec1, vec2, 0);
}

lemma vecDotProdZeroAux (vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecZero (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec2, i) == 0.0
decreases vecLength (vec1) - i
{}
