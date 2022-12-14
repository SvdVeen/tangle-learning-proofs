chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
subsection \<open>Parity Game Definitions\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"

text \<open>The empty dgraph is an empty set\<close>
definition empty_dgraph :: "'v dgraph" where
  "empty_dgraph \<equiv> {}"

definition V :: "'v dgraph \<Rightarrow> 'v set" where
  "V E = fst ` E \<union> snd ` E"

text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
type_synonym \<A> = "(int dgraph\<times>int set)"

definition \<A>E :: "\<A> \<Rightarrow> int dgraph" where
  "\<A>E a \<equiv> fst a"

definition \<A>V :: "\<A> \<Rightarrow> int set" where
  "\<A>V a \<equiv> V (\<A>E a)"

definition \<A>V\<^sub>0 :: "\<A> \<Rightarrow> int set" where
  "\<A>V\<^sub>0 a \<equiv> snd  a"

definition \<A>V\<^sub>1 :: "\<A> \<Rightarrow> int set" where
  "\<A>V\<^sub>1 a \<equiv> \<A>V a - \<A>V\<^sub>0 a"

text \<open>Just a quick test that I did this right: V should have no overlap with V.\<close>
lemma \<A>V\<^sub>0_\<A>V\<^sub>1_no_overlap: "\<forall>v\<in>(\<A>V\<^sub>0 a). v \<notin> (\<A>V\<^sub>1 a)"
  unfolding \<A>V\<^sub>0_def \<A>V\<^sub>1_def
  by auto
end
