module Theory.Theory.Module (
      ModuleType (..)
    , description
)
where

data ModuleType = ModuleSpthy | ModuleSpthyTyped | ModuleMsr | ModuleProverif | ModuleDeepSec 
instance Show ModuleType where
    show(ModuleSpthy) = "spthy"
    show(ModuleSpthyTyped) ="spthytyped"
    show(ModuleMsr) ="msr"
    show(ModuleProverif) ="proverif"
    show(ModuleDeepSec) ="deepsec"

description :: ModuleType -> String
description(ModuleSpthy) = "bbla"
