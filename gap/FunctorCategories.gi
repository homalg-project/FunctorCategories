# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#

####################################
#
# methods for operations:
#
####################################

##
InstallMethod( ApplyObjectInFunctorCategoryToObject,
        "for an object in a Hom-category and a CAP object",
        [ IsFunctorCategory, IsObjectInFunctorCategory, IsCapCategoryObject ],
        
  function ( Hom, F, objB )
    local pos;
    
    pos := SafePosition( SetOfObjects( Source( Hom ) ), objB );
    
    return ValuesOfFunctor( F )[1][pos];
    
end );

##
InstallOtherMethod( UnderlyingCapTwoCategoryCell,
        "for an object in a functor category",
        [ IsFunctorCategory, IsObjectInFunctorCategory ],
        
  function ( Hom, F )
    local values;
    
    values := ValuesOfFunctor( F );
    
    return CapFunctor( Source( Hom ), values[1], values[2], Target( Hom ) );
    
end );

##
InstallMethod( UnderlyingCapTwoCategoryCell,
        "for an object in a functor category",
        [ IsObjectInFunctorCategory ],
        
  function ( F )
    
    return UnderlyingCapTwoCategoryCell( CapCategory( F ), F );
    
end );

##
InstallMethod( ApplyObjectInFunctorCategoryToMorphism,
        "for an object in a Hom-category and a CAP morphism",
        [ IsFunctorCategory, IsObjectInFunctorCategory, IsCapCategoryMorphism ],
        
  function ( Hom, F, morB )
    local pos;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    pos := Position( SetOfGeneratingMorphisms( Source( Hom ) ), morB );
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    if IsInt( pos ) then
        return ValuesOfFunctor( F )[2][pos];
    fi;
    
    return FunctorMorphismOperation( UnderlyingCapTwoCategoryCell( Hom, F ) )(
                   ApplyObjectInFunctorCategoryToObject( Hom, F, Source( morB ) ),
                   morB,
                   ApplyObjectInFunctorCategoryToObject( Hom, F, Target( morB ) ) );
    
end );

##
InstallMethod( ApplyMorphismInFunctorCategoryToObject,
        "for a morphism in a Hom-category and a CAP object",
        [ IsFunctorCategory, IsMorphismInFunctorCategory, IsCapCategoryObject ],
        
  function ( Hom, eta, objB )
    local pos;
    
    pos := SafePosition( SetOfObjects( Source( Hom ) ), objB );
    
    return ValuesOnAllObjects( eta )[pos];
    
end );

##
InstallMethod( CallFuncList,
        "for an object in a functor category and a list",
        [ IsObjectInFunctorCategory, IsList ],
        
  function ( F, L )
    local Hom;
    
    Hom := CapCategory( F );
    
    if IsCapCategoryObject( L[1] ) then
        return ApplyObjectInFunctorCategoryToObject( Hom, F, L[1] );
    elif IsCapCategoryMorphism( L[1] ) then
        return ApplyObjectInFunctorCategoryToMorphism( Hom, F, L[1] );
    fi;
    
    Error( "the argument ", L[1], " is neither an object nor a morphism in ", Source( F ), "\n" );
    
end );

##
InstallMethod( CallFuncList,
        "for a morphism in a functor category and a list",
        [ IsMorphismInFunctorCategory, IsList ],
        
  function ( eta, L )
    
    if IsCapCategoryObject( L[1] ) then
        return ApplyMorphismInFunctorCategoryToObject( CapCategory( eta ), eta, L[1] );
    fi;
    
    Error( "the argument ", L[1], " is not an object in ", Source( Source( eta ) ), "\n" );
    
end );

##
InstallMethod( \.,
        "for an object in a functor category and positive integer",
        [ IsObjectInFunctorCategory, IsPosInt ],
        
  function ( F, string_as_int )
    
    return F( Source( F ).(NameRNam( string_as_int )) );
    
end );

##
InstallMethod( \.,
        "for a morphism in a functor category and positive integer",
        [ IsMorphismInFunctorCategory, IsPosInt ],
        
  function ( eta, string_as_int )
    
    return eta( Source( Source( eta ) ).(NameRNam( string_as_int )) );
    
end );

####################################
#
# methods for constructors:
#
####################################

##
InstallOtherMethodForCompilerForCAP( AsObjectInFunctorCategoryByValues,
        "for a functor category and two lists",
        [ IsFunctorCategory, IsList ],
        
  function ( Hom, values_of_functor )
    
    return CreateCapCategoryObjectWithAttributes( Hom,
                   Source, Source( Hom ),
                   Target, Target( Hom ),
                   ValuesOfFunctor, values_of_functor );
    
end );

##
InstallMethodForCompilerForCAP( AsObjectInFunctorCategoryByValues,
        "for a functor category and two lists",
        [ IsFunctorCategory, IsList, IsList ],
        
  function ( Hom, values_of_all_objects, values_of_all_generating_morphisms )
    
    return AsObjectInFunctorCategoryByValues( Hom,
                   Pair( values_of_all_objects, values_of_all_generating_morphisms ) );
    
end );

##
InstallMethodForCompilerForCAP( AsObjectInFunctorCategoryByFunctions,
        "for a functor category and two functions",
        [ IsFunctorCategory, IsFunction, IsFunction ],
        
  function ( Hom, functor_on_objects, functor_on_generating_morphisms )
    local defining_triple, nr_objs, nr_mors, mors, values_of_all_objects, values_of_all_generating_morphisms;
    
    defining_triple := DefiningTripleOfUnderlyingQuiver( Source( Hom ) );
    
    nr_objs := defining_triple[1];
    nr_mors := defining_triple[2];
    mors := defining_triple[3];
    
    values_of_all_objects := LazyHList( [ 1 .. nr_objs ], o -> functor_on_objects( o ) );
    values_of_all_generating_morphisms := LazyHList( [ 1 .. nr_mors ], m -> functor_on_generating_morphisms(
                                                  functor_on_objects( 1 + mors[m][1] ),
                                                  m,
                                                  functor_on_objects( 1 + mors[m][2] ) ) );
    
    return AsObjectInFunctorCategoryByValues( Hom, values_of_all_objects, values_of_all_generating_morphisms );
    
end );

##
InstallOtherMethod( AsObjectInFunctorCategory,
        "for a functor category and a CAP functor",
        [ IsFunctorCategory, IsCapFunctor ],
        
  function ( Hom, F )
    local B, objs, mors, functor_on_objects, functor_on_generating_morphism;
    
    B := Source( Hom );
    
    objs := SetOfObjects( B );
    mors := SetOfGeneratingMorphisms( B );
    
    functor_on_objects := objB_index -> FunctorObjectOperation( F )( objs[objB_index] );
    functor_on_generating_morphism := { source, morB_index, range } -> FunctorMorphismOperation( F )( source, mors[morB_index], range );
    
    return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_generating_morphism );
    
end );

##
InstallMethod( AsObjectInFunctorCategory,
        "for a CAP functor",
        [ IsCapFunctor ],
        
  function ( F )
    local Hom;
    
    Hom := FunctorCategory( SourceOfFunctor( F ), RangeOfFunctor( F ) );
    
    return AsObjectInFunctorCategory( Hom, F );
    
end );

##
InstallMethod( AsObjectInFunctorCategory,
        "for a CAP category, a record (of images of objects) and a record (of images of morphisms)",
        [ IsCapCategory, IsRecord, IsRecord ],
        
  function ( B, rec_images_of_objects, rec_images_of_morphisms )
    
    return AsObjectInFunctorCategory( CapFunctor( B, rec_images_of_objects, rec_images_of_morphisms ) );
    
end );

##
InstallMethod( AsObjectInFunctorCategory,
        "for a CAP category, a list (of images of objects) and a list (of images of morphisms)",
        [ IsCapCategory, IsList, IsList ],
        
  function ( B, images_of_objects, images_of_morphisms )
    
    if IsEmpty( images_of_objects ) then
        Error( "the list of images is empty\n" );
    fi;
    
    return AsObjectInFunctorCategory( CapFunctor( B, images_of_objects, images_of_morphisms, CapCategory( images_of_objects[1] ) ) );
    
end );

##
InstallMethod( AsObjectInFunctorCategory,
        "for a functor category and two lists",
        [ IsFunctorCategory and HasRangeCategoryOfHomomorphismStructure, IsList, IsList ],
        
  function ( Hom, dims, matrices )
    local kmat, objects, morphisms, k, mat;
    
    if dims = [ ] then
        Error( "the list of dimensions is empty\n" );
    elif not IsInt( dims[1] ) then
        Error( "expecting a list of integers as the second argument but received ", dims, "\n" );
    fi;
    
    kmat := RangeCategoryOfHomomorphismStructure( Hom );
    
    if not ( IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) ) then
        TryNextMethod( );
    fi;
    
    objects := List( dims, dim -> dim / kmat );
    
    morphisms := SetOfGeneratingMorphisms( Source( Hom ) );
    
    k := CommutativeRingOfLinearCategory( kmat );
    
    mat :=
      function ( m )
        local source, target;
        
        source := VertexIndex( UnderlyingVertex( Source( morphisms[m] ) ) );
        target := VertexIndex( UnderlyingVertex( Target( morphisms[m] ) ) );
        
        if IsHomalgMatrix( matrices[m] ) then
            m := matrices[m];
        else
            m := HomalgMatrix( One( k ) * matrices[m], dims[source], dims[target], k );
        fi;
        
        return m / kmat;
        
    end;
    
    morphisms := List( [ 1 .. Length( morphisms ) ], mat );
    
    return AsObjectInFunctorCategoryByValues( Hom, objects, morphisms );
    
end );

##
InstallOtherMethodForCompilerForCAP( AsMorphismInFunctorCategoryByValues,
        "for a functor category, two objects in the functor category, and a list",
        [ IsFunctorCategory, IsObjectInFunctorCategory, IsList, IsObjectInFunctorCategory ],
        
  function ( Hom, source, values_on_all_objects, range )
    
    return CreateCapCategoryMorphismWithAttributes( Hom,
                   source,
                   range,
                   ValuesOnAllObjects, values_on_all_objects );
    
end );

##
InstallOtherMethodForCompilerForCAP( AsMorphismInFunctorCategory,
        "for a functor category, two objects in the functor category, and a function",
        [ IsFunctorCategory, IsObjectInFunctorCategory, IsFunction, IsObjectInFunctorCategory ],
        
  function ( Hom, source, natural_transformation_on_objects, range )
    local nr_objs, source_values, range_values, values_on_all_objects;
    
    nr_objs := DefiningTripleOfUnderlyingQuiver( Source( Hom ) )[1];
    
    source_values := ValuesOfFunctor( source )[1];
    range_values := ValuesOfFunctor( range )[1];
    
    values_on_all_objects := LazyHList( [ 1 .. nr_objs ],
                                     o -> natural_transformation_on_objects( source_values[o], o, range_values[o] ) );
    
    return AsMorphismInFunctorCategoryByValues( Hom, source, values_on_all_objects, range );
    
end );

##
InstallOtherMethodForCompilerForCAP( AsMorphismInFunctorCategory,
        "for a functor category and a CAP natural transformation",
        [ IsFunctorCategory, IsCapNaturalTransformation ],
        
  function ( Hom, eta )
    local B, objs;
    
    B := Source( Hom );
    
    objs := SetOfObjects( B );
    
    return AsMorphismInFunctorCategory( Hom,
                   AsObjectInFunctorCategory( Source( eta ) ),
                   { source, objB_index, range } -> NaturalTransformationOperation( eta )( source, objs[objB_index], range ),
                   AsObjectInFunctorCategory( Target( eta ) ) );
    
end );

##
InstallMethod( AsMorphismInFunctorCategory,
        "for a CAP natural transformation",
        [ IsCapNaturalTransformation ],
        
  function ( eta )
    local F, Hom;
    
    F := Source( eta );
    
    Hom := FunctorCategory( SourceOfFunctor( F ), RangeOfFunctor( F ) );
    
    return AsMorphismInFunctorCategory( Hom, eta );
    
end );

##
InstallMethod( AsMorphismInFunctorCategory,
        "for a record and two objects in Hom-category",
        [ IsObjectInFunctorCategory, IsRecord, IsObjectInFunctorCategory ],
        
  function ( U, e, V )
    local eta;

    eta := NaturalTransformation(
                   e,
                   UnderlyingCapTwoCategoryCell( U ),
                   UnderlyingCapTwoCategoryCell( V ) );
    
    return AsMorphismInFunctorCategory( eta );
    
end );

##
InstallMethod( AsMorphismInFunctorCategory,
        "for two objects in a functor category and a list",
        [ IsObjectInFunctorCategory, IsList, IsObjectInFunctorCategory ],
        
  function ( U, e, V )
    local kmat;
    
    if not IsEmpty( e ) and IsHomalgMatrix( e[1] ) then
        
        kmat := Target( U );
        
        e := List( e, mat -> mat / kmat );
        
    fi;
    
    return AsMorphismInFunctorCategoryByValues( CapCategory( U ), U, e, V );
    
end );

##
InstallMethodWithCache( FunctorCategory,
        "for a CAP category",
        [ IsCapCategory, IsCapCategory ],
        
  function( B, D )
    local object_datum_type, object_constructor, object_datum,
          morphism_datum_type, morphism_constructor, morphism_datum,
          B_op, defining_triple, PSh,
          modeling_tower_object_constructor, modeling_tower_object_datum,
          modeling_tower_morphism_constructor, modeling_tower_morphism_datum,
          Hom, properties, doctrines, name;
    
    ##
    object_datum_type :=
      CapJitDataTypeOfNTupleOf( 2,
              CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( D ) ),
              CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( D ) ) );
    
    ##
    object_constructor := AsObjectInFunctorCategoryByValues;
    
    ##
    object_datum := { Hom, o } -> ValuesOfFunctor( o );
    
    ##
    morphism_datum_type :=
      CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( D ) );
    
    ##
    morphism_constructor := AsMorphismInFunctorCategoryByValues;
    
    ##
    morphism_datum := { Hom, m } -> ValuesOnAllObjects( m );
    
    ## building the categorical tower:
    
    if IsFpCategory( B ) then
        B_op := OppositeFpCategory( B : FinalizeCategory := true );
    elif IsCategoryFromNerveData( B ) then
        B_op := OppositeCategoryFromNerveData( B : FinalizeCategory := true );
    elif IsCategoryFromDataTables( B ) then
        B_op := OppositeCategoryFromDataTables( B : FinalizeCategory := true );
    elif HasIsInitialCategory( B ) and IsInitialCategory( B ) then
        B_op := Opposite( B : FinalizeCategory := true );
    elif HasIsFiniteCategory( B ) and IsFiniteCategory( B ) then
        B_op := OppositeFiniteCategory( B : FinalizeCategory := true );
    elif IsAlgebroid( B ) or IsAlgebroidFromDataTables( B ) then
        B_op := OppositeAlgebroid( B : FinalizeCategory := true );
    else
        Error( "the first argument must be in { IsFpCategory, IsCategoryFromNerveData, IsCategoryFromDataTables, IsFinite, IsInitialCategory, IsAlgebroid }\n" );
    fi;
    
    PSh := PreSheaves( B_op, D : FinalizeCategory := true );
    
    ## from the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function( Hom, pair )
        local PSh;
        
        PSh := ModelingCategory( Hom );
        
        return ObjectConstructor( PSh, pair );
        
    end;
    
    ## from the object in the modeling category to the raw object data
    modeling_tower_object_datum :=
      function( Hom, obj )
        local PSh;
        
        PSh := ModelingCategory( Hom );
        
        return ObjectDatum( PSh, obj );
        
    end;
    
    ## from the raw morphism data to the morphism in the modeling category
    modeling_tower_morphism_constructor :=
      function( Hom, source, images, range )
        local PSh;
        
        PSh := ModelingCategory( Hom );
        
        return MorphismConstructor( PSh, source, images, range );
        
    end;
    
    ## from the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( Hom, mor )
        local PSh;
        
        PSh := ModelingCategory( Hom );
        
        return MorphismDatum( PSh, mor );
        
    end;
    
    ##
    Hom :=
      ReinterpretationOfCategory( PSh,
              rec( name := Concatenation( "FunctorCategory( ", Name( B ), ", ", Name( D ), " )" ),
                   category_filter := IsFunctorCategory,
                   category_object_filter := IsObjectInFunctorCategory,
                   category_morphism_filter := IsMorphismInFunctorCategory,
                   object_datum_type := object_datum_type,
                   morphism_datum_type := morphism_datum_type,
                   object_constructor := object_constructor,
                   object_datum := object_datum,
                   morphism_constructor := morphism_constructor,
                   morphism_datum := morphism_datum,
                   modeling_tower_object_constructor := modeling_tower_object_constructor,
                   modeling_tower_object_datum := modeling_tower_object_datum,
                   modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                   modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                   only_primitive_operations := true )
              : FinalizeCategory := false );
    
    if HasIsMonoidalCategory( D ) and IsMonoidalCategory( D ) and
       HasCounit( B ) and HasComultiplication( B ) then
        
        properties := [ "IsMonoidalCategory",
                        #"IsBraidedMonoidalCategory",
                        #"IsSymmetricMonoidalCategory",
                        #"IsClosedMonoidalCategory",
                        #"IsSymmetricClosedMonoidalCategory",
                        #"IsRigidSymmetricClosedMonoidalCategory",
                        ];
        
        doctrines := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "doctrines", [ ] );
        
        if not doctrines = [ ] and IsStringRep( doctrines ) then
            doctrines := [ doctrines ];
        fi;
        
        Append( properties, doctrines );
        
        for name in Intersection( ListKnownCategoricalProperties( D ), properties ) do
            name := ValueGlobal( name );
            
            Setter( name )( Hom, name( D ) );
            
        od;
        
        AddTensorUnit( Hom,
          function ( Hom )
            local B, D, I_D, functor_on_objects, counit, id, mors, functor_on_morphisms;
            
            B := Source( Hom );
            D := Target( Hom );
            
            I_D := TensorUnit( D );
            
            functor_on_objects := objB_index -> I_D;
            
            counit := Counit( B );
            
            id := IdentityMorphism( D, I_D );
            
            mors := SetOfGeneratingMorphisms( B );
            
            functor_on_morphisms :=
              function ( new_source, morB_index, new_range )
                local coef;
                
                coef := Coefficients( UnderlyingQuiverAlgebraElement( ApplyFunctor( counit, mors[morB_index] ) ) );
                
                if Length( coef ) = 1 then
                    coef := coef[1];
                elif coef = [ ] then
                    coef := 0;
                else
                    Error( "the list coef has more than one entry\n" );
                fi;
                
                return coef * id;
                
            end;
            
            return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
            
        end );
        
        AddTensorProductOnObjects( Hom,
          function ( Hom, F, G )
            local B, D, F_o_vals, G_o_vals, functor_on_objects, comult, mors, functor_on_morphisms;
            
            B := Source( Hom );
            D := Target( Hom );
            
            F_o_vals := ValuesOfFunctor( F )[1];
            G_o_vals := ValuesOfFunctor( G )[1];
            
            functor_on_objects := objB_index -> TensorProductOnObjects( D, F_o_vals[objB_index], G_o_vals[objB_index] );
            
            comult := Comultiplication( B );
            
            mors := SetOfGeneratingMorphisms( B );
            
            functor_on_morphisms :=
              function ( new_source, morB_index, new_range )
                local Delta;
                
                Delta := ApplyFunctor( comult, mors[morB_index] );
                
                Delta := DecompositionOfMorphismInSquareOfAlgebroid( Delta );
                
                return Sum( List( Delta,
                               s -> s[1] * PreComposeList( D, List( s[2],
                                       t -> TensorProductOnMorphisms( D, F( t[1] ), G( t[2] ) ) ) ) ) );
                
            end;
            
            return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
            
        end );
        
        AddDualOnObjects( Hom,
          function ( Hom, F )
            local B, D, F_o_vals, functor_on_objects, antipode, mors, functor_on_morphisms;
            
            B := Source( Hom );
            D := Target( Hom );
            
            F_o_vals := ValuesOfFunctor( F )[1];
            
            functor_on_objects := objB_index -> DualOnObjects( D, F_o_vals[objB_index] );
            
            antipode := Antipode( B );
            
            mors := SetOfGeneratingMorphisms( B );
            
            functor_on_morphisms :=
              function ( new_source, morB_index, new_range )
                local S;
                
                S := DecompositionOfMorphismInAlgebroid( ApplyFunctor( antipode, mors[morB_index] ) );
                
                return Sum( List( S,
                               s -> s[1] * PreComposeList( D, List( s[2],
                                       t -> DualOnMorphisms( D, F( t ) ) ) ) ) );
                
            end;
            
            return AsObjectInFunctorCategoryByFunctions( Hom, functor_on_objects, functor_on_morphisms );
            
        end );
        
    fi;
    
    SetSource( Hom, B );
    SetTarget( Hom, D );
    
    SetOppositeOfSource( Hom, B_op );
    
    Append( Hom!.compiler_hints.category_attribute_names,
            [ "Source",
              "Target",
              "OppositeOfSource",
              ] );
    
    if not HasRangeCategoryOfHomomorphismStructure( Hom ) and
       (HasIsInitialCategory and IsInitialCategory)( B ) then
        
        SET_RANGE_CATEGORY_Of_HOMOMORPHISM_STRUCTURE( Hom, Hom );
        
    fi;
    
    Finalize( Hom );
    
    return Hom;
    
end );

##
InstallMethodWithCache( FunctorCategory,
        "for a CAP category and a homalg field",
        [ IsAlgebroid, IsHomalgRing and IsFieldForHomalg ],
        
  function ( B, k )
    local kmat, Hom;
    
    if HasRangeCategoryOfHomomorphismStructure( B ) then
        
        kmat := RangeCategoryOfHomomorphismStructure( B );
        
    else
        
        kmat := CategoryOfRows( k );
        
    fi;
    
    Assert( 0, IsMatrixCategory( kmat ) or IsCategoryOfRows( kmat ) );
    
    CapCategorySwitchLogicOn( kmat );
    
    Hom := FunctorCategory( B, kmat );
    
    CapCategorySwitchLogicOn( Hom );
    
    return Hom;
    
end );

##
InstallMethod( FunctorCategory,
        "for a CAP category",
        [ IsCapCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function( B )
    
    return FunctorCategory( B, RangeCategoryOfHomomorphismStructure( B ) );
    
end );

##
InstallMethod( Hom,
        "for two CAP categories",
        [ IsCapCategory, IsCapCategory ],
        
  FunctorCategory );

##
InstallMethod( Hom,
        "for a CAP category and a homalg field",
        [ IsAlgebroid, IsHomalgRing and IsFieldForHomalg ],
        
  FunctorCategory );

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for a functor category",
        [ IsFunctorCategory ],
        
  function( Hom )
    
    return SetOfObjectsOfCategory( Hom );
    
end );

##
InstallMethodForCompilerForCAP( SetOfGeneratingMorphisms,
        "for a functor category",
        [ IsFunctorCategory ],
        
  function( Hom )
    
    return SetOfGeneratingMorphismsOfCategory( Hom );
    
end );

####################################
#
# Methods for attributes
#
####################################

##
InstallMethodForCompilerForCAP( YonedaEmbeddingDataInFunctorCategory,
        [ IsCapCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B_op )
    local B, Hom, objs, mors, name, Yoneda_on_objs, Yoneda_on_mors;
    
    if IsFpCategory( B_op ) then
        B := OppositeFpCategory( B_op : FinalizeCategory := true );
    elif IsAlgebroid( B_op ) then
        B := OppositeAlgebroid( B_op : FinalizeCategory := true );
    else
        Error( "the input must either be IsFpCategory or is IsAlgebroid\n" );
    fi;
    
    Hom := FunctorCategory( B );
    
    objs := SetOfObjects( B_op );
    
    mors := SetOfGeneratingMorphisms( B_op );
    
    Yoneda_on_objs :=
      function ( obj )
        local Yobj;
        
        Yobj := AsObjectInFunctorCategoryByValues( Hom,
                        List( objs, o -> HomomorphismStructureOnObjects( B_op, o, obj ) ),
                        List( mors, m -> HomomorphismStructureOnMorphisms( B_op, m, IdentityMorphism( B_op, obj ) ) ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        SetIsProjective( Yobj, true );
        
        return Yobj;
        
    end;
    
    Yoneda_on_mors :=
      function ( s, mor, r )
        
        return AsMorphismInFunctorCategoryByValues( Hom,
                       s,
                       List( objs, o -> HomomorphismStructureOnMorphisms( B_op, IdentityMorphism( B_op, o ), mor ) ),
                       r );
        
    end;
    
    return Pair( Yoneda_on_objs, Yoneda_on_mors );
    
end );

##
InstallMethod( YonedaEmbeddingInFunctorCategory,
        [ IsCapCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B_op )
    local B, Hom, Yoneda, Yoneda_data;
    
    if IsFpCategory( B_op ) then
        B := OppositeFpCategory( B_op : FinalizeCategory := true );
    elif IsAlgebroid( B_op ) then
        B := OppositeAlgebroid( B_op : FinalizeCategory := true );
    else
        Error( "the input must either be IsFpCategory or is IsAlgebroid\n" );
    fi;
    
    Hom := FunctorCategory( B );
    
    Yoneda := CapFunctor( "Yoneda embedding functor", B_op, Hom );
    
    Yoneda_data := YonedaEmbeddingDataInFunctorCategory( B_op );
    
    AddObjectFunction( Yoneda, Yoneda_data[1] );
    
    AddMorphismFunction( Yoneda,  Yoneda_data[2] );
    
    return Yoneda;
    
end );

##
InstallMethod( YonedaEmbeddingOfOppositeOfSourceCategory,
        "for a functor category",
        [ IsFunctorCategory ],
        
  function ( Hom )
    
    return YonedaEmbeddingInFunctorCategory( OppositeOfSource( Hom ) );
    
end );

##
InstallMethod( \.,
        "for a functor category and a positive integer",
        [ IsFunctorCategory, IsPosInt ],
        
  function( Hom, string_as_int )
    local name, opY, F, opYc;
    
    name := NameRNam( string_as_int );
    
    opY := YonedaEmbeddingOfOppositeOfSourceCategory( Hom );
    
    F := SourceOfFunctor( opY );
    
    opYc := opY( F.(name) );
    
    if IsObjectInPreSheafCategory( opYc ) then
        
        SetIsProjective( opYc, true );
        
    elif IsMorphismInPreSheafCategory( opYc ) then
        
        if CanCompute( Hom, "IsMonomorphism" ) then
            IsMonomorphism( opYc );
        fi;
        
        if CanCompute( Hom, "IsSplitMonomorphism" ) then
            IsSplitMonomorphism( opYc );
        fi;
        
        if CanCompute( Hom, "IsEpimorphism" ) then
            IsEpimorphism( opYc );
        fi;
        
        if CanCompute( Hom, "IsSplitEpimorphism" ) then
            IsSplitEpimorphism( opYc );
        fi;
        
        ## IsIsomorphism = IsSplitMonomorphism and IsSplitEpimorphism
        ## we add this here in case the logic is deactivated
        if CanCompute( Hom, "IsIsomorphism" ) then
            IsIsomorphism( opYc );
        fi;
        
    fi;
    
    return opYc;
    
end );

##
InstallMethodForCompilerForCAP( YonedaProjection,
        [ IsFpCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    local Hom, Yepis, N1, N2, pt;
    
    Hom := FunctorCategory( B );
    
    Yepis := YonedaNaturalEpimorphisms( B );
    
    ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ), where
    ## Hom(-, c) := ⊔_{a ∈ B} Hom(a, c),
    ## Hom(-, ψ) := ⊔_{a ∈ B} Hom(id_a, ψ):
    N1 := AsObjectInFunctorCategoryByValues( Hom, Yepis[2][1], Yepis[2][2] );
    
    ## The 2-Yoneda functor B → H, c ↦ Hom(-, -) × Hom(-, c) and ψ ↦ Hom(-, -) × Hom(-, ψ), where
    ## Hom(-, -) × Hom(-, c) := ⊔_{a ∈ B} ⊔_{b ∈ B} Hom(a, b) × Hom(b, c),
    ## Hom(-, -) × Hom(-, ψ) := ⊔_{a ∈ B} ⊔_{b ∈ B} Hom(id_a, id_b) × Hom(id_b, ψ):
    N2 := AsObjectInFunctorCategoryByValues( Hom, Yepis[3][1], Yepis[3][2] );
    
    ## The Yoneda projection is a natrual epimorphism from the 2-Yoneda functor to the Yoneda functor
    ## B → H, c ↦ Hom(-, -) × Hom(-, c) and ψ ↦ Hom(-, -) × Hom(-, ψ)
    pt := AsMorphismInFunctorCategoryByValues( Hom,
                  N2,   ## The 2-Yoneda functor: B → H, c ↦ Hom(-, -) × Hom(-, c) and ψ ↦ Hom(-, -) × Hom(-, ψ)
                  Yepis[4],
                  N1 ); ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ)
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    SetIsEpimorphism( pt, true );
    
    return pt;
    
end );

##
InstallMethodForCompilerForCAP( YonedaComposition,
        [ IsFpCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    local Hom, Yepis, H, N1, N2, mu;
    
    Hom := FunctorCategory( B );
    
    Yepis := YonedaNaturalEpimorphisms( B );
    
    ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ), where
    ## Hom(-, c) := ⊔_{a ∈ B} Hom(a, c),
    ## Hom(-, ψ) := ⊔_{a ∈ B} Hom(id_a, ψ):
    N1 := AsObjectInFunctorCategoryByValues( Hom, Yepis[2][1], Yepis[2][2] );
    
    ## The 2-Yoneda functor B → H, c ↦ Hom(-, -) × Hom(-, c) and ψ ↦ Hom(-, -) × Hom(-, ψ), where
    ## Hom(-, -) × Hom(-, c) := ⊔_{a ∈ B} ⊔_{b ∈ B} Hom(a, b) × Hom(b, c),
    ## Hom(-, -) × Hom(-, ψ) := ⊔_{a ∈ B} ⊔_{b ∈ B} Hom(id_a, id_b) × Hom(id_b, ψ):
    N2 := AsObjectInFunctorCategoryByValues( Hom, Yepis[3][1], Yepis[3][2] );
    
    ## The Yoneda composition is a natrual epimorphism from the 2-Yoneda functor to the Yoneda functor
    ## Hom(-, -) × Hom(-, c) ↠ Hom(-, c):
    mu := AsMorphismInFunctorCategoryByValues( Hom,
                  N2, ## The 2-Yoneda functor: B → H, c ↦ Hom(-, -) × Hom(-, c) and ψ ↦ Hom(-, -) × Hom(-, ψ)
                  Yepis[5],
                  N1 ); ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ)
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    SetIsEpimorphism( mu, true );
    
    return mu;
    
end );

##
InstallMethodForCompilerForCAP( YonedaFibration,
        [ IsCapCategory and IsFiniteCategory ],
        
  function ( B )
    local Hom, Yepis, H, N0, N1;
    
    Hom := FunctorCategory( B );
    
    Yepis := YonedaNaturalEpimorphisms( B );
    
    ## The constant functor of 0-cells B → H, c ↦ B_0, ψ ↦ id_{B_0}
    N0 := AsObjectInFunctorCategoryByValues( Hom, Yepis[1][1], Yepis[1][2] );
    
    ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ), where
    ## Hom(-, c) := ⊔_{a ∈ B} Hom(a, c),
    ## Hom(-, ψ) := ⊔_{a ∈ B} Hom(id_a, ψ):
    N1 := AsObjectInFunctorCategoryByValues( Hom, Yepis[2][1], Yepis[2][2] );
    
    ## The source fibration is a natrual morphism from the Yoneda functor to the constant functor of 0-cells
    ## Hom(-, c) → B_0:
    return AsMorphismInFunctorCategoryByValues( Hom,
                   N1, ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ)
                   Yepis[6],
                   N0 ); ## The constant functor of 0-cells
    
end );

####################################
#
# View, Print, Display and LaTeX methods:
#
####################################

##
InstallMethod( ViewString,
        [ IsObjectInFunctorCategory ],
        
  function ( F )
    local algebroid, vertices, arrows, v_dim, v_string, a_dim, a_string, string;
    
    if not (IsMatrixCategory( Target( CapCategory( F ) ) ) or IsCategoryOfRows( Target( CapCategory( F ) ) )) then
        TryNextMethod();
    fi;
    
    algebroid := Source( CapCategory( F ) );
    
    vertices := List( SetOfObjects( algebroid ), UnderlyingVertex );
    
    v_dim := List( ValuesOfFunctor( F )[1], ObjectDatum );
    
    v_string := ListN( vertices, v_dim, { vertex, dim } -> Concatenation( "(", String( vertex ), ")->", String( dim ) ) );
    
    v_string := JoinStringsWithSeparator( v_string, ", " );
    
    arrows := List( SetOfGeneratingMorphisms( algebroid ), UnderlyingQuiverAlgebraElement );
    
    if not IsPathAlgebra( UnderlyingQuiverAlgebra( algebroid ) ) then
      
      arrows := List( arrows, a -> Paths( Representative( a ) )[ 1 ] );
      
    else
      
      arrows := List( arrows, a -> Paths( a )[ 1 ] );
      
    fi;
    
    a_dim := List( ValuesOfFunctor( F )[2], m -> [ ObjectDatum( Source( m ) ), ObjectDatum( Target( m ) ) ] );
    
    a_string := ListN( arrows, a_dim,
                  { arrow, dim } -> Concatenation(
                      "(", String( arrow ), ")->", String( dim[ 1 ] ), "x", String( dim[ 2 ] ) )
                    );
    
    a_string := JoinStringsWithSeparator( a_string, ", " );
    
    string := Concatenation( v_string, "; ", a_string );
    
    return Concatenation( "<", string, ">" );
    
end );

##
InstallMethod( DisplayString,
        [ IsObjectInFunctorCategory ],
        
  function ( F )
    local objects, images_of_objects, string, i, morphisms, images_of_morphisms;
    
    objects := SetOfObjects( Source( F ) );
    
    images_of_objects := ValuesOfFunctor( F )[1];
    
    string := "";
    
    for i in [ 1 .. Length( objects ) ] do
        
        string := Concatenation( string,
                          "Image of ", ViewString( objects[i] ), ":\n",
                          StringDisplay( images_of_objects[i] ),
                          "\n" );
        
    od;
    
    morphisms := SetOfGeneratingMorphisms( Source( F ) );
    
    images_of_morphisms := ValuesOfFunctor( F )[2];
    
    for i in [ 1 .. Length( morphisms ) ] do
        
        string := Concatenation( string,
                          "Image of ", StringView( morphisms[i] ), ":\n",
                          StringDisplay( images_of_morphisms[i] ),
                          "\n" );
        
    od;
    
    return Concatenation( string,
                   "An object in ", Name( CapCategory( F ) ), " given by the above data\n" );
    
end );

##
InstallMethod( ViewString,
        [ IsMorphismInFunctorCategory ],
        
  function ( eta )
    local vertices, s_dim, r_dim, string;
    
    if not (IsMatrixCategory( Target( CapCategory( eta ) ) ) or IsCategoryOfRows( Target( CapCategory( eta ) ) )) then
        TryNextMethod();
    fi;
    
    vertices := List( SetOfObjects( Source( Source( eta ) ) ), UnderlyingVertex );
     
    s_dim := List( ValuesOfFunctor( Source( eta ) )[1], ObjectDatum );
    
    r_dim := List( ValuesOfFunctor( Target( eta ) )[1], ObjectDatum );
   
    string := ListN( vertices, s_dim, r_dim,
                { vertex, s, r } ->
                    Concatenation( "(", String( vertex ), ")->", String( s ), "x", String( r ) ) );
    
    string := JoinStringsWithSeparator( string, ", " );
    
    return Concatenation( "<", string, ">" );
    
end );

##
InstallMethod( DisplayString,
        [ IsMorphismInFunctorCategory ],
        
  function ( eta )
    local objects, images_of_objects, string, i;
    
    objects := SetOfObjects( Source( Source( eta ) ) );
    
    images_of_objects := ValuesOnAllObjects( eta );
    
    string := "";
    
    for i in [ 1 .. Length( objects ) ] do
        
        string := Concatenation( string,
                          "Image of ", ViewString( objects[i] ), ":\n",
                          StringDisplay( images_of_objects[i] ),
                          "\n" );
        
    od;
    
    return Concatenation( string,
                   "A morphism in ", Name( CapCategory( eta ) ), " given by the above data\n" );
    
end );

##
InstallMethod( LaTeXOutput,
          [ IsObjectInFunctorCategory ],
          
  function( F )
    local objs, v_objs, mors, v_mors, s, i;
    
    objs := SetOfObjects( Source( F ) );
    v_objs := ValuesOfFunctor( F )[1];
    
    mors := SetOfGeneratingMorphisms( Source( F ) );
    v_mors := ValuesOfFunctor( F )[2];
    
    s := "\\begin{array}{ccc}\n ";
    
    for i in [ 1 .. Length( objs ) ] do
      
      s := Concatenation(
              s,
              LaTeXOutput( objs[ i ] ),
              " & \\mapsto & ",
              LaTeXOutput( v_objs[ i ] ),
              " \\\\ "
            );
      
    od;
    
    s := Concatenation( s, "\\hline & & \\\\" );
    
    for i in [ 1 .. Length( mors ) ] do
      
      s := Concatenation(
              s,
              LaTeXOutput( mors[ i ] : OnlyDatum := true ),
              " & \\mapsto & ",
              LaTeXOutput( v_mors[ i ] : OnlyDatum := false ),
              " \\\\ & & \\\\"
            );
    od;
    
    s := Concatenation( s, "\\end{array}" );
    
    return s;
    
end );

##
InstallMethod( LaTeXOutput,
          [ IsMorphismInFunctorCategory ],
          
  function( eta )
    local only_datum, objs, v_objs, i, datum;
    
    only_datum := ValueOption( "OnlyDatum" );
    
    objs := SetOfObjects( Source( Source( eta ) ) );
    
    v_objs := ValuesOnAllObjects( eta );
    
    datum := "\\begin{array}{ccc}\n";
    
    for i in [ 1 .. Length( objs ) ] do
      
      datum := Concatenation(
                  datum,
                  LaTeXOutput( objs[ i ] ),
                  " & \\mapsto & ",
                  LaTeXOutput( v_objs[ i ] : OnlyDatum := false ),
                  " \\\\ & & \\\\" );
    
    od;
    
    datum := Concatenation( datum, "\\end{array}" );
    
    if only_datum = true then
      
      return datum;
      
    else
      
      return Concatenation(
                LaTeXOutput( Source( eta ) ),
                "\\xrightarrow{",
                datum,
                "}",
                LaTeXOutput( Target( eta ) )
              );
    
    fi;
    
end );
