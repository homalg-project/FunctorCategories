# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Declarations
#

#! @Chapter Category of presheaves of a finitely presented (linear) category

####################################
#
#! @Section &GAP; Categories
#
####################################

#! @Description
#!  The &GAP; category of a presheaf category.
#! @Arguments category
DeclareCategory( "IsPreSheafCategory",
        IsCapCategory );

#! @Description
#!  The &GAP; category of cells in a presheaf category.
#! @Arguments cell
DeclareCategory( "IsCellInPreSheafCategory",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of objects in a presheaf category.
#! @Arguments obj
DeclareCategory( "IsObjectInPreSheafCategory",
        IsCellInPreSheafCategory and
        IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a presheaf category.
#! @Arguments mor
DeclareCategory( "IsMorphismInPreSheafCategory",
        IsCellInPreSheafCategory and
        IsCapCategoryMorphism );

####################################
#
#! @Section Attributes
#
####################################

##
DeclareAttribute( "DefiningPairOfUnderlyingQuiver",
        IsPreSheafCategory );

CapJitAddTypeSignature( "DefiningPairOfUnderlyingQuiver", [ IsPreSheafCategory ],
  function ( input_types )
    
    Assert( 0, IsPreSheafCategory( input_types[1].category ) );
    
    return rec( filter := IsNTuple,
                element_types :=
                [ rec( filter := IsInt ),
                  rec( filter := IsList, element_type := rec( filter := IsNTuple, element_types := [ rec( filter := IsInt ), rec( filter := IsInt ) ] ) ) ] );
    
end );

#! @Arguments PSh
DeclareAttribute( "Source",
        IsPreSheafCategory );

CapJitAddTypeSignature( "Source", [ IsPreSheafCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( Source( input_types[1].category ) );
    
end );

#! @Arguments PSh
DeclareAttribute( "Range",
        IsPreSheafCategory );

CapJitAddTypeSignature( "Range", [ IsPreSheafCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( Range( input_types[1].category ) );
    
end );

#! @Description
#!  The source of the presheaf <A>F</A>.
#! @Arguments F
#! @Returns a &CAP; category
DeclareAttribute( "Source",
        IsObjectInPreSheafCategory );

CapJitAddTypeSignature( "Source", [ IsObjectInPreSheafCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( Source( input_types[1].category ) );
    
end );

#! @Description
#!  The target of the presheaf <A>F</A>.
#! @Arguments F
#! @Returns a &CAP; category
DeclareAttribute( "Range",
        IsObjectInPreSheafCategory );

CapJitAddTypeSignature( "Range", [ IsObjectInPreSheafCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( Range( input_types[1].category ) );
    
end );

#! @Description
#!  Apply the functor <A>F</A> (as an object in the corresponding Hom-category) to the cell <A>c</A>.
#!  The shorthand is <A>F</A>(<A>c</A>).
#! @Arguments F, c
#! @Returns a &CAP; cell
DeclareOperation( "ApplyObjectInPreSheafCategoryToObject",
        [ IsPreSheafCategory, IsObjectInPreSheafCategory, IsCapCategoryObject ] );

DeclareOperation( "ApplyObjectInPreSheafCategoryToMorphism",
        [ IsPreSheafCategory, IsObjectInPreSheafCategory, IsCapCategoryMorphism ] );

#!  The 2-cell underlying the functor object <A>F_or_eta</A>.
#! @Arguments F_or_eta
#! @Returns a &CAP; functor or natural transformation
DeclareAttribute( "UnderlyingCapTwoCategoryCell",
        IsCellInPreSheafCategory );

#! @Description
#!  Apply the natural transformation <A>eta</A> (as an object in the corresponding Hom-category) to the object <A>o</A>.
#!  The shorthand is <A>eta</A>(<A>o</A>).
#! @Arguments eta, o
DeclareOperation( "ApplyMorphismInPreSheafCategoryToObject",
        [ IsPreSheafCategory, IsMorphismInPreSheafCategory, IsCapCategoryObject ] );

##
DeclareAttribute( "ValuesOfPreSheaf",
        IsObjectInPreSheafCategory );

CapJitAddTypeSignature( "ValuesOfPreSheaf", [ IsObjectInPreSheafCategory ],
  function ( input_types )
    
    Assert( 0, IsPreSheafCategory( input_types[1].category ) );
    
    return rec( filter := IsNTuple,
                element_types :=
                [ rec( filter := IsList, element_type := CapJitDataTypeOfObjectOfCategory( Range( input_types[1].category ) ) ),
                  rec( filter := IsList, element_type := CapJitDataTypeOfMorphismOfCategory( Range( input_types[1].category ) ) ) ] );
    
end );

#! @Description
#!  Returns the values of the presheaf morphism <A>eta</A> on all objects of the source category of presheaf category <A>PSh</A>.
#! @Arguments eta
#! @Returns a list
DeclareAttribute( "ValuesOnAllObjects",
        IsMorphismInPreSheafCategory );

CapJitAddTypeSignature( "ValuesOnAllObjects", [ IsMorphismInPreSheafCategory ],
  function ( input_types )
    
    Assert( 0, IsPreSheafCategory( input_types[1].category ) );
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfMorphismOfCategory( Range( input_types[1].category ) ) );
    
end );

##
DeclareAttribute( "YonedaEmbeddingDataInPreSheafCategory",
        IsCapCategory );

##
DeclareAttribute( "YonedaEmbeddingInPreSheafCategory",
        IsCapCategory );

##
DeclareAttribute( "YonedaEmbeddingOfSourceCategory",
        IsPreSheafCategory );

#! @Description
#!  The input is a category <A>B</A> with finitely many objects equipped with
#!  a homomorphism structure with values in a finite complete and finite cocomplete category <A>H</A>.
#!  The output is the nerve of <A>B</A> truncated in degree $2$,
#!  as an object in the category of presheaves on <C>SimplicialCategoryTruncatedInDegree</C>($2$)
#!  with values in <A>H</A>.
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "NerveTruncatedInDegree2", IsCapCategory );
#! @InsertChunk NerveTruncatedInDegree2

####################################
#
#! @Section Constructors
#
####################################

DeclareOperation( "CreatePreSheafByValues", [ IsPreSheafCategory, IsList, IsList ] );

DeclareOperation( "CreatePreSheafByFunctions", [ IsPreSheafCategory, IsFunction, IsFunction ] );

#! @Description
#!  Turn the functor <C><A>F</A>:<A>B</A>^op</C> $\to$ <C>C</C> into an object in the category of functors <C><A>PSh</A> := PreSheaves( <A>B</A>, C )</C>.
#! @Arguments PSh, values_of_all_objects, values_of_all_generating_morphisms
#! @Returns a presheaf
#! @Group CreatePreSheaf

#! @Arguments F
#! @Group CreatePreSheaf
DeclareAttribute( "CreatePreSheaf",
        IsCapFunctor );

#! @Description
#!  An alternative input is the source category <A>B</A> and two defining records <A>rec_images_of_objects</A> and <A>rec_images_of_morphisms</A> of <A>F</A>.
#! @Arguments B, rec_images_of_objects, rec_images_of_morphisms
#! @Group CreatePreSheaf
DeclareOperation( "CreatePreSheaf",
        [ IsCapCategory, IsRecord, IsRecord ] );

#! @Description
#!  Another alternative input is the source category <A>B</A> and two defining lists <A>images_of_objects</A> and <A>images_of_morphisms</A> of <A>F</A>.
#!  The order of their entries must correspond to that of the vertices and arrows of the underlying quiver.
#!
#!  For the convenience of the user the following input is also valid:
#!  If <A>images_of_objects</A> is a list of nonnegative integers,
#!  <A>images_of_morphisms</A> is a list of matrices, and
#!  $k:=$ <C>CommutativeRingOfLinearCategory</C>( B ) is a field
#!  then the two lists are interpreted as objects and morphisms
#!  in <C>MatrixCategory</C>( $k$ ), respectively.
#! @Arguments B, images_of_objects, images_of_morphisms
#! @Group CreatePreSheaf
if false then
DeclareOperation( "CreatePreSheaf",
        [ IsCapCategory, IsList, IsList ] );
fi;

#! @Description
#! @Returns a morphism in a &CAP; category
#! @Group CreatePreSheafMorphism
DeclareOperation( "CreatePreSheafMorphismByValues",
        [ IsPreSheafCategory, IsObjectInPreSheafCategory, IsList, IsObjectInPreSheafCategory ] );

#! @Description
#!  Turn the natrual transformation <A>eta</A>:$F \to G$ into a morphism
#!  <C><A>U</A> := AsObjectInFunctorCategory( F )</C> $\to$ <C><A>V</A> := AsObjectInFunctorCategory( G )</C>
#!  in the category of functors <C><A>Hom</A> := Hom( B, C )</C>, where
#!  <C>B := Source( F ) = Source( G )</C> and <C>C := Range( F ) = Range( G )</C>.
#! @Arguments eta
#! @Group CreatePreSheafMorphism
DeclareAttribute( "CreatePreSheafMorphism",
        IsCapNaturalTransformation );

#!  Another alternative input is the triple (<A>U</A>, <A>e</A>, <A>V</A>),
#!  where <A>e</A> is a defining list of <A>eta</A>.
#! @Arguments U, e, V
#! @Group CreatePreSheafMorphism
DeclareOperation( "CreatePreSheafMorphism",
        [ IsObjectInPreSheafCategory, IsList, IsObjectInPreSheafCategory ] );

#! @Arguments U, e, V
#!  An alternative input is the triple (<A>U</A>, <A>e</A>, <A>V</A>),
#!  where <A>e</A> is a defining record of <A>eta</A>.
#! @Group CreatePreSheafMorphism
DeclareOperation( "CreatePreSheafMorphism",
        [ IsObjectInPreSheafCategory, IsRecord, IsObjectInPreSheafCategory ] );

#! @Group CreatePreSheafMorphism
DeclareOperation( "CreatePreSheafMorphismByFunction",
        [ IsObjectInPreSheafCategory, IsFunction, IsObjectInPreSheafCategory ] );

#! @Description
#!  Construct a presheaf category.
#! @Returns a &CAP; category
#! @Arguments B
#! @Group PreSheafCategory
DeclareOperation( "PreSheafCategory",
        [ IsCapCategory ] );

DeclareOperationWithCache( "PreSheafCategory",
        [ IsCapCategory, IsCapCategory ] );