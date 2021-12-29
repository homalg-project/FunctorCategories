#! @Chunk S3

LoadPackage( "FunctorCategories" );

#! @Example
q := RightQuiver( "q(1)[a:1->1,b:1->1]" );
#! q(1)[a:1->1,b:1->1]
S3 := Category( q, [ [ q.a^2, q.1 ] , [ q.b^3, q.1 ], [ q.bab, q.a ] ] );
#! Monoid generated by the right quiver q(1)[a:1->1,b:1->1]
#! with relations [ a*a = 1, b*b*b = 1, b*a*b = a ]
Q := HomalgFieldOfRationals( );
#! Q
QS3 := Q[S3];
#! Algebroid generated by the right quiver q(1)[a:1->1,b:1->1]
Qmat := MatrixCategory( Q );
#! Category of matrices over Q
FunCat := FunctorCategory( QS3, Qmat );
#! The category of functors: Bialgebroid generated by the right quiver
#! q(1)[a:1->1,b:1->1] -> Category of matrices over Q
CommutativeRingOfLinearCategory( FunCat );
#! Q
Y := YonedaEmbedding( QS3 );
#! Yoneda embedding functor
Y1 := Y( QS3.1 );
#! <(1)->6; (a)->6x6, (b)->6x6>
#! @EndExample