#! @Chapter Precompilation

#! @Section Precompiling the category of finite quivers

#! @Example

LoadPackage( "FunctorCategories", false );
#! true

LoadPackage( "CompilerForCAP", ">= 2022.11-03", false );
#! true

ReadPackage( "FinSetsForCAP", "gap/CompilerLogic.gi" );
#! true

ReadPackage( "Algebroids", "gap/CompilerLogic.gi" );
#! true

ReadPackage( "FunctorCategories", "gap/CompilerLogic.gi" );
#! true

category_constructor := { } -> CategoryOfQuiversEnrichedOver( CategoryOfSkeletalFinSets( : FinalizeCategory := true ) );;

given_arguments := [ ];;
compiled_category_name := "FinQuiversPrecompiled";;
package_name := "FunctorCategories";;

CapJitPrecompileCategoryAndCompareResult(
    category_constructor,
    given_arguments,
    package_name,
    compiled_category_name
   : operations := [ "InitialObject",
                     "Coproduct",
                     #"InjectionOfCofactorOfCoproductWithGivenCoproduct",
                     #"UniversalMorphismFromCoproductWithGivenCoproduct",
                     #"CoproductOnMorphismsWithGivenCoproducts", # <- derived and leads to an error
                     #"CoproductFunctorialWithGivenCoproducts", # <- derived
                     "DistinguishedObjectOfHomomorphismStructure",
                     "HomomorphismStructureOnObjects",
                     #"HomomorphismStructureOnMorphismsWithGivenObjects",
                     "InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism",
                     "MorphismsOfExternalHom",
                     ]
);;

FinQuiversPrecompiled( );
#! CategoryOfQuiversEnrichedOver( SkeletalFinSets )

CategoryOfQuiversEnrichedOver( SkeletalFinSets )!.precompiled_functions_added;
#! true

#! @EndExample
