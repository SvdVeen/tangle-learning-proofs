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
definition is_succ :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_succ E v w \<equiv> w \<in> succs E v"

lemma "w \<in> succs E v \<Longrightarrow> is_succ E v w"
  unfolding is_succ_def succs_def by auto

definition subgraph_node :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v dgraph" where
  "subgraph_node E v \<equiv> E-{e | e. fst e = v \<or> snd e = v}"

(* Obvious lemma to show this definition is right*)
lemma "E' = subgraph_node E v \<Longrightarrow> v \<notin> fst`E' \<union> snd`E'"
  unfolding subgraph_node_def by auto

definition subgraph_edge :: "'v dgraph \<Rightarrow> ('v\<times>'v) \<Rightarrow> 'v dgraph" where
  "subgraph_edge E e \<equiv> E-{e}"

(* Obvious lemma to show this definition is right*)
lemma "e \<notin> subgraph_edge E e"
  unfolding subgraph_edge_def by auto

definition restrict_graph :: "'v dgraph \<Rightarrow> 'v set \<Rightarrow> 'v dgraph" where
  "restrict_graph E V \<equiv> E \<inter> V\<times>V"

definition induced_subgraph_node :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v dgraph" where
  "induced_subgraph_node E v \<equiv> E-{e | e. snd e \<notin> E\<^sup>*``{v}}"

(* Probably not phrased right, applying auto gives a step that wants me to prove false *)
lemma "E' = induced_subgraph_node E v \<Longrightarrow> w \<in> (fst`E' \<union> snd`E') \<Longrightarrow> w \<in> E\<^sup>*``{v}"
  unfolding induced_subgraph_node_def
  apply auto
  oops

definition induced_subgraph_edge :: "'v dgraph \<Rightarrow> ('v\<times>'v) \<Rightarrow> 'v dgraph" where
  "induced_subgraph_edge E e \<equiv> induced_subgraph_node E (snd e)"

context
  fixes E :: "'v dgraph"
begin
  fun path :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path v [] v' \<longleftrightarrow> v = v'"
  |  "path v (x#xs) v' \<longleftrightarrow> (v,x) \<in> E \<and> path x xs v'"

  definition cycle_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_node v xs \<equiv> path v xs v \<and> xs \<noteq> []"

  definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_from_node v xs \<equiv> \<exists>v'. (v,v')\<in>E\<^sup>* \<and> cycle_node v' xs"

  text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
  type_synonym 'a strat = "'a \<Rightarrow> 'a option"

  definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
    "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"
end

locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"

  definition top_priority :: "'v list \<Rightarrow> nat" where
    "top_priority xs \<equiv> MAX v \<in> set xs. prio v"

  abbreviation winning_even :: "'v list \<Rightarrow> bool" where
    "winning_even xs \<equiv> even (top_priority xs)"

  abbreviation winning_odd :: "'v list \<Rightarrow> bool" where
    "winning_odd xs \<equiv> odd (top_priority xs)"

  definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S"

  definition induced_by_strategy :: "'v strat \<Rightarrow> 'v dgraph" where
    "induced_by_strategy \<sigma> = E \<inter> ((-dom \<sigma>) \<times> UNIV \<union> E_of_strat \<sigma>)"

  lemma "induced_by_strategy \<sigma> \<subseteq> E"
    unfolding induced_by_strategy_def by auto

  definition won_by_even :: "'v \<Rightarrow> bool" where
    "won_by_even v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and> 
(\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_even xs)"

  definition won_by_odd :: "'v \<Rightarrow> bool" where
    "won_by_odd v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and> 
(\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_odd xs)"

lemma w1: "won_by_even v \<Longrightarrow> \<not>won_by_odd v"
  unfolding won_by_even_def won_by_odd_def apply auto sorry

lemma w2: "won_by_even v \<or> won_by_odd v" sorry

lemma "won_by_even v \<noteq> won_by_odd v" using w1 w2 by blast 


end

text \<open>
  A play is an infinite sequence \<pi>\<in>V\<omega> of moves along the edges of the graph in the arena.
  A winning play for player 0 is a play where the maximum priority seen infinitely often is even.
\<close>
text \<open>We represent paths with an infinite co-inductive list. 
  Still testing how this works. A lazy list might work better?\<close>
codatatype (infset: 'a) inflist = InfCons (head: 'a) (tail: "'a inflist")

primcorec iedges :: "'a inflist \<Rightarrow> ('a\<times>'a) inflist" where
  "iedges l = InfCons (head l, head (tail l)) (iedges (tail l))"
(* Just some shorthand *)
definition iedgeset :: "'a inflist \<Rightarrow> ('a\<times>'a) set" where
  "iedgeset l \<equiv> infset (iedges l)"

(* TO DO: sanity check lemmas for the above two definitions *)

definition iappend :: "'a list \<Rightarrow> 'a inflist \<Rightarrow> 'a inflist" where "iappend = foldr InfCons"

lemma [simp]: "iappend [] xs = xs" unfolding iappend_def by simp
lemma [simp]: "iappend (x#xs) ys = InfCons x (iappend xs ys)" unfolding iappend_def by simp

lemma "iappend (xs@ys) zs = iappend xs (iappend ys zs)"
  by (induction xs) auto

primcorec ireplicate :: "'a \<Rightarrow> 'a inflist" where
  "ireplicate x = InfCons x (ireplicate x)"

context 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

  (*
  
    v\<^sub>0 v\<^sub>1 v\<^sub>2 \<dots>
    
    R v\<^sub>i v\<^sub>i\<^sub>+\<^sub>1
    
    path u (v#vs) \<longleftrightarrow> R u v \<and> path v vs
  *)

  coinductive is_ipath :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "R u v \<Longrightarrow> is_ipath v vs \<Longrightarrow> is_ipath u (InfCons v vs)"

lemma "R x x \<Longrightarrow> vs=ireplicate x \<Longrightarrow> is_ipath x vs"
  apply (coinduction)
  using ireplicate.code by fastforce
lemma "R x x \<Longrightarrow> is_ipath x (ireplicate x)"
  apply coinduction
  using ireplicate.code by fastforce
(*
    apply (rule is_ipath.coinduct[where X="\<lambda>x vs. R x x \<and> vs=ireplicate x"])
    apply simp
    apply simp
    subgoal for xx
      apply (rule exI[where x=xx])
      apply (rule exI[where x="ireplicate xx"])
      apply simp
      by (rule ireplicate.ctr)
    done
*)
(*
  primcorec pathmap :: "('b \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 'b inflist \<Rightarrow> nat" where
    "pathmap f vs = f (head vs) (pathmap f (tail vs))"
  
  
  primcorec path :: "'a inflist \<Rightarrow> bool" where
    "path vs \<longleftrightarrow> undefined (path (tail vs))"

  
  
  primcorec path :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "path u vs \<longleftrightarrow> R u (head vs) \<and> path (head vs) (tail vs)"
  
    
  primcorec path :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "path u (InfCons v vs) \<longleftrightarrow> R u v \<and> path v vs"
*)  


end

(*
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

type_synonym 'v path = "'v llist" *)

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
  unfolding V\<^sub>1_def by auto

definition connected where "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"
  
lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V"
  unfolding connected_def V_def
  by (metis Range.RangeI Range_snd UnCI rtranclE)

(* An attempt to translate the is_ipath from above into the context of the arena *)
coinductive is_play :: "'v \<Rightarrow> 'v inflist \<Rightarrow> bool" where
  "v \<in> succs E u \<Longrightarrow> is_play v vs \<Longrightarrow> is_play u (InfCons v vs)"

lemma "is_play u vs \<Longrightarrow> u\<in>V"
  using is_play.simps unfolding succs_def V_def
  by (metis Image_singleton_iff UnI1 fst_conv imageI)

lemma "is_play u (InfCons v vs) \<Longrightarrow> v\<in>V"
  using is_play.simps unfolding succs_def V_def
  by (metis ImageE UnI2 imageI inflist.inject snd_conv)

(* Wouldn't it be nice to have a definition that shows whether any path is a valid play?  *)
coinductive is_play_2 :: "'v inflist \<Rightarrow> bool" where
  "v\<in>V \<Longrightarrow> (v,w) \<in> E \<Longrightarrow> is_play_2 (InfCons v (InfCons w vs))"

find_theorems is_play_2

(* These are just the same lemmas as above, translated for is_play_2 *)
lemma "is_play_2 (InfCons v vs) \<Longrightarrow> v\<in>V"
  using is_play_2.simps unfolding V_def by blast

lemma "is_play_2 (InfCons u (InfCons v vs)) \<Longrightarrow> v\<in>V"
  using is_play_2.simps unfolding V_def apply simp
  by (metis image_eqI snd_conv)

(* A play contains no dead ends. *)
lemma no_dead_ends:"is_play_2 vs \<Longrightarrow> \<forall>v\<in>infset vs. succs E v \<noteq> {}"
  using succ unfolding succs_def by auto

(* This one is very obvious but I'm just trying things here *)
lemma "is_play_2 (InfCons u (InfCons v vs)) \<Longrightarrow> (u,v)\<in>E"
  using is_play_2.simps by blast

(* Not sure if this is actually useful at all, and the proof is clearly a huge mess. *)
lemma "is_play_2 vs \<Longrightarrow> \<forall>v\<in>infset vs. v\<in>V"
  using is_play_2.simps unfolding V_def
  by (metis Image_singleton_iff Un_iff equals0I fst_conv imageI succ)
  
definition all_plays :: "'v inflist set" where
  "all_plays \<equiv> {p | p. is_play_2 p}"

lemma "p \<in> all_plays \<Longrightarrow> is_play_2 p"
  unfolding all_plays_def by auto

(* Hopefully limits a set of plays to the plays induced by an edge. *)
definition induced_plays :: "'v inflist set \<Rightarrow> ('v\<times>'v) \<Rightarrow> 'v inflist set" where
  "induced_plays P e \<equiv> P-{p | p. p \<in> P \<and> e \<notin> iedgeset p}"

text \<open>
  A winning play for the even player is a play in which the highest priority that occurs
  infinitely often is even
\<close>

(*TO DO*)



primcorec induced_play :: "'v \<Rightarrow> 'v strat \<Rightarrow> 'v inflist" where
  "induced_play v s = InfCons v (induced_play (s v) s)"

(*
  If a strategy always gives successors from E, then the induced play is a valid one.
  BUT: this also assumes the strategy gives moves for both players, which is not quite right.
*)
lemma "\<forall>v\<in>V. (s::'v strat) v\<in>V \<and> (v, s v)\<in>E \<Longrightarrow> u\<in>V \<Longrightarrow> is_play_2 (induced_play u s)"
  apply (coinduction)
  by (metis induced_play.ctr)
(*TO DO*)

end
  
end
