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

lemma vecDotProdAuxSymm (vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec2, i) == vecDotProdAux (vec2, vec1, i)
decreases vecLength (vec1) - i
{}

lemma vecDotProdSymm (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vec1, vec2) == vecDotProd (vec2, vec1)
{
    vecDotProdAuxSymm (vec1, vec2, 0);
}

lemma vecDotProdAuxDist (vec1 : Vector, vec2 : Vector, vec3 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vecAdd (vec2, vec3), i) == 
    vecDotProdAux (vec1, vec2, i) + vecDotProdAux (vec1, vec3, i)
decreases vecLength (vec1) - i
{
    if i == vecLength (vec1) {

    }
    else {
        vecDotProdAuxDist (vec1, vec2, vec3, i + 1);
    }
}

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

lemma vecNormDist (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecNorm (vecAdd (vec1, vec2)) == vecNorm (vec1) + 2.0 * vecDotProd (vec1, vec2) + vecNorm (vec2)
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
    assert vecGet (res1, 0) == x1 + x2;
    assert forall i | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (res1, i) == 
            vecGet (vec1, i - 1) + vecGet (vec2, i - 1);    
}
