open List
open Position
open Exceptions

type positionplusinit = InitPos |  Pos of int list

let posplusinit2string  = function InitPos -> "Init"
                         | Pos p   -> pos2string p

let posplusinit2pos  = function InitPos -> raise (ImplementationError "pos2string cannot convert this, this should never happen")

                     | Pos p   -> p

type t = positionplusinit

let compare (s1:positionplusinit) (s2:positionplusinit) = match (s1,s2) with
    (InitPos,InitPos) -> 0
  | (InitPos,Pos _) -> -1
  | (Pos _, InitPos) -> 1
  | (Pos p1, Pos p2) -> Position.compare p1 p2

