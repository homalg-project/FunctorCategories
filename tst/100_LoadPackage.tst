# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# This file tests if the package can be loaded without errors or warnings.
#
# do not load suggested dependencies automatically
gap> PushOptions( rec( OnlyNeeded := true ) );
gap> package_loading_info_level := InfoLevel( InfoPackageLoading );;
gap> SetInfoLevel( InfoPackageLoading, PACKAGE_ERROR );;
gap> LoadPackage( "Digraphs", false );
true
gap> LoadPackage( "ToolsForCategoricalTowers", false );
true
gap> LoadPackage( "FinSetsForCAP", false );
true
gap> LoadPackage( "Locales", false );
true
gap> LoadPackage( "FreydCategoriesForCAP", false );
true
gap> LoadPackage( "IO_ForHomalg", false );
true
gap> LoadPackage( "FunctorCategories", false );
true
gap> SetInfoLevel( InfoPackageLoading, PACKAGE_INFO );;
gap> LoadPackage( "Digraphs" );
true
gap> LoadPackage( "ToolsForCategoricalTowers" );
true
gap> LoadPackage( "FinSetsForCAP" );
true
gap> LoadPackage( "Locales" );
true
gap> LoadPackage( "FreydCategoriesForCAP" );
true
gap> LoadPackage( "IO_ForHomalg" );
true
gap> LoadPackage( "FunctorCategories" );
true
gap> SetInfoLevel( InfoPackageLoading, package_loading_info_level );;
gap> HOMALG_IO.show_banners := false;;
