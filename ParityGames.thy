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
  
  
locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"

end

locale arena = arena_defs E V\<^sub>0 
  for  
    E :: "'v dgraph"
  and V\<^sub>0 :: "'v set"  
  + 
  assumes V0_ss: "V\<^sub>0 \<subseteq> V"
  assumes succ: "E``{v}\<noteq>{}"
  
  assumes fin: "finite (UNIV::'v set)"
  
  
begin
  
  definition "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"

  
  lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V" sorry
  

end
  
lemma 
  assumes "arena (\<A>E \<A>) (\<A>V\<^sub>0 \<A>)"  
  assumes "v\<in>\<A>V \<A>" "(v,v')\<in>(\<A>E \<A>)\<^sup>*"  
  shows "v'\<in>\<A>V \<A>"
proof -
  interpret arena "\<A>E \<A>" "\<A>V\<^sub>0 \<A>" by fact

  thm conn
  from assms conn show ?thesis
    unfolding V_def \<A>V_def ParityGames.V_def connected_def by blast
qed  

  



  
end
