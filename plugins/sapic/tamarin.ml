open Formula
open Fact
open Action

type term = Term.term
type var = Var.var
type termlist = term list

type msr = factlist*actionlist*factlist

type rule = {identifier: string; let_block: string; rule_body: msr}

