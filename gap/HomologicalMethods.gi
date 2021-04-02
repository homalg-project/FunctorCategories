




##
InstallMethod( RadicalInclusion,
          [ IsCapCategoryObjectInHomCategory ],
          
  function( F )
    local algebroid, objs, mors, val_objs, val_mors, pos, im, RF;
    
    algebroid := SourceOfFunctor( UnderlyingCapTwoCategoryCell( F ) );
    
    objs := SetOfObjects( algebroid );
    
    mors := SetOfGeneratingMorphisms( algebroid );
    
    val_objs := ValuesOnAllObjects( F );
    
    val_mors := ValuesOnAllGeneratingMorphisms( F );
    
    pos := List( objs, o -> PositionsProperty( mors, m -> IsEqualForObjects( o, Range( m ) ) ) );
    
    im := List( pos, p -> val_mors{ p } );
    
    im :=
      ListN( im, val_objs,
        function( l, o )
          if IsEmpty( l ) then
            return UniversalMorphismFromZeroObject( o );
          else
            return ImageEmbedding( MorphismBetweenDirectSums( TransposedMat( [ l ] ) ) );
          fi;
        end
      );
      
    val_objs := List( im, Source );
    
    val_mors :=
      ListN( mors, val_mors,
        function( m, vm )
          local s, r;
          s := Position( objs, Source( m ) );
          r := Position( objs, Range( m ) );
          return LiftAlongMonomorphism( im[ r ], PreCompose( im[ s ], vm ) );
        end
      );
      
    RF := AsObjectInHomCategory( algebroid, val_objs, val_mors );
    
    return AsMorphismInHomCategory( RF, im, F );
    
end );

##
InstallMethod( CoverElementByProjectiveObject,
          [ IsCapCategoryObjectInHomCategory, IsCapCategoryMorphism, IsInt ],
  function( F, l, n )
    local Hom, algebroid, vertices, v, P_v, val_objs;
    
    Hom := CapCategory( F );
    
    algebroid := Source( Hom );
    
    vertices := SetOfObjects( algebroid );
     
    v := vertices[ n ];
     
    P_v := IndecProjectiveObjects( Hom )[ n ];
    
    val_objs := List( vertices, u -> List( BasisOfExternalHom( v, u ), b -> PreCompose( l, F( b ) ) ) );
    
    val_objs := ListN(
                  ValuesOnAllObjects( P_v ),
                  val_objs,
                  ValuesOnAllObjects( F ),
                  { s, rows, r } -> MorphismBetweenDirectSums( s, TransposedMat( [ rows ] ), r )
                );
                
    return AsMorphismInHomCategory( P_v, val_objs, F );
    
end );

##
InstallMethod( MorphismsFromDirectSumDecompositionOfProjectiveCover,
          [ IsCapCategoryObjectInHomCategory ],
  function( F )
    local Hom, matrix_cat, k, i_F, pi_i_F, pre_images, dec;
    
    Hom := CapCategory( F );
    
    if not IsAdmissibleQuiverAlgebra( UnderlyingQuiverAlgebra( Source( Hom ) ) ) then
      
      TryNextMethod( );
      
    fi;
    
    matrix_cat := Range( Hom );
    
    k := 1 / matrix_cat;
    
    i_F := RadicalInclusion( F );
    
    pi_i_F := CokernelProjection( i_F );
    
    pre_images := List( ValuesOnAllObjects( pi_i_F ), m -> Lift( IdentityMorphism( Range( m ) ), m ) );
    
    dec :=
      ListN( pre_images, [ 1 .. Length( pre_images ) ],
        function( pre_image, i )
          local m, n, D, iotas;
          
          n := Dimension( Source( pre_image ) );
          
          D := ListWithIdenticalEntries( n, k );
          
          iotas := List( [ 1 .. n ], j -> PreCompose( InjectionOfCofactorOfDirectSum( D, j ), pre_image ) );
          
          return List( iotas, iota -> CoverElementByProjectiveObject( F, iota, i ) );
          
        end
      );
      
    return Concatenation( dec );
    
end );

##
InstallMethod( DirectSumDecompositionOfProjectiveObject,
          [ IsCapCategoryObjectInHomCategory ], # and IsProjective
    MorphismsFromDirectSumDecompositionOfProjectiveCover
);

##
InstallMethod( ProjectiveCover,
          [ IsCapCategoryObjectInHomCategory ],
  function( F )
    local dec, sources, D, m, pi_F;
    
    dec := MorphismsFromDirectSumDecompositionOfProjectiveCover( F );
    
    sources := List( dec, Source );
    
    if IsEmpty( sources ) then
      
      D := ZeroObject( CapCategory( F ) );
      
      m := [ ];
      
    else
      
      D := DirectSum( sources );
      
      m := List( [ 1 .. Size( sources ) ], i -> InjectionOfCofactorOfDirectSumWithGivenDirectSum( sources, i, D ) );
      
    fi;
     
    pi_F := MorphismBetweenDirectSums( D, TransposedMat( [ dec ] ), F );
    
    # Source( pi_F ) = D but they might not be identical gap objects, hence
    SetMorphismsFromDirectSumDecompositionOfProjectiveCover( Source( pi_F ), m );
    
    return pi_F;
    
end );

##
InstallMethod( DualOfObjectInHomCategory,
          [ IsCapCategoryObjectInHomCategory ],
          
  function( F )
    local H, A_oid, kvec, A_oid_op, H_op, images_of_morphisms, D_F;
    
    H := CapCategory( F );
    
    A_oid := Source( H );
    
    kvec := Range( H );
    
    if not IsMatrixCategory( kvec ) then
      
      Error( "The range category should be a category of matrices" );
      
    fi;
    
    A_oid_op := OppositeAlgebroidOverOppositeQuiverAlgebra( A_oid );
    
    H_op := Hom( A_oid_op, kvec );
    
    images_of_morphisms := List( ValuesOnAllGeneratingMorphisms( F ), v -> TransposedMatrix( UnderlyingMatrix( v ) ) / kvec );
    
    D_F := AsObjectInHomCategory( A_oid_op, ValuesOnAllObjects( F ), images_of_morphisms );
    
    SetDualOfObjectInHomCategory( D_F, F );
    
    return D_F;
    
end );

##
InstallMethod( DualOfMorphismInHomCategory,
          [ IsCapCategoryMorphismInHomCategory ],
          
  function( eta )
    local F, G, H_op, A_oid_op, kvec, images_of_objects, D_eta;
    
    F := DualOfObjectInHomCategory( Source( eta ) );
    
    G := DualOfObjectInHomCategory( Range( eta ) );
    
    H_op := CapCategory( F );
    
    A_oid_op := Source( H_op );
    
    kvec := Range( H_op );
    
    images_of_objects := List( ValuesOnAllObjects( eta ), v -> TransposedMatrix( UnderlyingMatrix( v ) ) / kvec );
    
    D_eta := AsMorphismInHomCategory( G, images_of_objects, F );
    
    SetDualOfMorphismInHomCategory( D_eta, eta );
    
    return D_eta;
    
end );


##
InstallMethod( MorphismsIntoDirectSumDecompositionOfInjectiveEnvelope,
          [ IsCapCategoryObjectInHomCategory ],
          
  F -> List(
            MorphismsFromDirectSumDecompositionOfProjectiveCover( DualOfObjectInHomCategory( F ) ),
            DualOfMorphismInHomCategory
          )
);

##
InstallMethod( DirectSumDecompositionOfInjectiveObject,
          [ IsCapCategoryObjectInHomCategory ],
          
  F -> List(
            DirectSumDecompositionOfProjectiveObject( DualOfObjectInHomCategory( F ) ),
            DualOfMorphismInHomCategory
          )
);

##
InstallMethod( InjectiveEnvelope,
          [ IsCapCategoryObjectInHomCategory ],
          
  F -> DualOfMorphismInHomCategory( ProjectiveCover( DualOfObjectInHomCategory( F ) ) )
);
