open Formula
open Fact
open Action

type term = Term.term
type var = Var.var
type termlist = term list

type msr = factlist*actionlist*factlist

type rule = {identifier: string; let_block: string; rule_body: msr}

let print_rule rule = 
            match rule.rule_body with
            (l,a,r) -> 
                Printf.sprintf "rule %s:%s \n [%s] --[%s]-> [%s]\n\n" (rule.identifier) rule.let_block (facts2string l) (action_list2string a) (facts2string r) 


