chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
subsection \<open>Parity Game Definitions\<close>
text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"
definition succs :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "succs E v \<equiv> E``{v}"

locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"
end

text \<open>
  A play is an infinite sequence \<pi>\<in>V\<omega> of moves along the edges of the graph in the arena.
  A winning play for player 0 is a play where the maximum priority seen infinitely often is even.
\<close>
(*text \<open>We represent paths with an infinite coinductive list. Still testing how this works. A lazy list might work better?\<close>
codatatype (infset: 'a) inflist = InfCons (head: 'a) (tail: "'a inflist")*)
text \<open>We can use a coinductive list to represent paths. This definition is taken from the datypes documentation of Isabelle.\<close>
codatatype (lset: 'a) llist =
  lnull: LNil
| LCons (lhd: 'a) (ltl: "'a llist")
for
  map: lmap
  rel: llist_all2
  pred: llist_all
where
  "ltl LNil = LNil"

type_synonym 'v path = "'v llist"

text \<open>
  A strategy for player i is a function \<sigma>:V*Vi\<rightarrow>V that selects a successor for every history of the
  play ending in a vertex of player i.
  A strategy is memoryless iff \<sigma>(wv) = \<sigma>(v) for all w\<in>V*, v\<in>Vi.
  A strategy is winning from a vertex v if all plays starting in v and consistent with \<sigma> are winning
  for player i.
\<close>

locale arena = arena_defs E V\<^sub>0 
  for  
    E :: "'v dgraph"
  and V\<^sub>0 :: "'v set"  
  + 
  assumes V0_ss: "V\<^sub>0 \<subseteq> V"
  assumes succ: "E``{v}\<noteq>{}"
  assumes fin: "finite (UNIV::'v set)"
begin

text \<open>Wholly unnecessary but allows me to not have to unfold V1_def all the time.\<close>
lemma V1_ss[simp]: "V\<^sub>1 \<subseteq> V"
  unfolding V\<^sub>1_def
  by auto

definition connected where "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"
  
lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V"
  unfolding connected_def V_def
  by (metis Range.RangeI Range_snd UnCI rtranclE)

primcorec a_path :: "'v path \<Rightarrow> bool" where
  "a_path LNil \<longleftrightarrow> false"
| "a_path (LCons _ LNil) \<longleftrightarrow> false"
| "a_path (LCons v vs) \<longleftrightarrow> (v\<in>V \<and> (a_path vs))"

coinductive is_path :: "'v path \<Rightarrow> bool" where
nil: "\<not>is_path LNil" |
cons_nil: "\<not>is_path (LCons _ LNil)" |
cons: "v\<in>V \<and> is_path vs \<Longrightarrow> is_path (LCons v vs)"

end
  
end
