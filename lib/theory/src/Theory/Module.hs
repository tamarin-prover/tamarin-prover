module Theory.Module (
      ModuleType (..)
    , description
)
where

data ModuleType = ModuleSpthy | ModuleSpthyTyped | ModuleMsr | ModuleProVerif | ModuleDeepSec
  deriving (Eq, Ord, Enum, Bounded)
instance Show ModuleType where
    show(ModuleSpthy) = "spthy"
    show(ModuleSpthyTyped) ="spthytyped"
    show(ModuleMsr) ="msr"
    show(ModuleProVerif) ="proverif"
    show(ModuleDeepSec) ="deepsec"

description :: ModuleType -> String
description(ModuleSpthy) = "spthy (including Sapic Processes)"
description(ModuleSpthyTyped) ="spthy with explicit types inferred"
description(ModuleMsr) ="pure msrs (with Sapic translation)"
description(ModuleProVerif) ="ProVerif"
description(ModuleDeepSec) ="DeepSec"
