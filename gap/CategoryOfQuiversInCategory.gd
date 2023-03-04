# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Declarations
#

#! @Chapter The category of quivers in a category

####################################
#
#! @Section &GAP; Categories
#
####################################

#! @Description
#!  The &GAP; category of the category of quivers in a category.
#! @Arguments category
DeclareCategory( "IsCategoryOfQuiversInCategory",
        IsCapCategory );

#! @Description
#!  The &GAP; category of cells in the category of quivers in a category.
#! @Arguments cell
DeclareCategory( "IsCellInCategoryOfQuiversInCategory",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of objects in the category of quivers in a category.
#! @Arguments obj
DeclareCategory( "IsObjectInCategoryOfQuiversInCategory",
        IsCellInCategoryOfQuiversInCategory and
        IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in the category of quivers in a category.
#! @Arguments mor
DeclareCategory( "IsMorphismInCategoryOfQuiversInCategory",
        IsCellInCategoryOfQuiversInCategory and
        IsCapCategoryMorphism );

####################################
#
#! @Section Constructors
#
####################################

#! @Description
#!  Construct the category of quivers in the category <A>C</A>.
#! @Returns a &CAP; category
#! @Arguments C
DeclareAttribute( "CategoryOfQuivers",
        IsCapCategory );
#! @InsertChunk CategoryOfQuiversInFinBouquets
#! @InsertChunk CategoryOfQuiversInFinReflexiveQuivers

#!
DeclareOperation( "CreateQuiverInCategory",
        [ IsCategoryOfQuiversInCategory, IsList ] );

#!
DeclareOperation( "CreateQuiverMorphismInCategory",
        [ IsObjectInCategoryOfQuiversInCategory, IsList ] );
