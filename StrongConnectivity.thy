theory StrongConnectivity
  imports Main Digraphs
begin
section \<open>Strongly Connected Graphs\<close>
(** A non-empty graph E with vertices V is strongly connected if for all pairs of vertices in the
    graph, there exists a path from one to the other and vice-versa.
    We do not have to specify the path from v' to v, as it follows from the definition. *)
definition strongly_connected :: "'v dgraph \<Rightarrow> 'v set \<Rightarrow> bool" where
  "strongly_connected E V \<equiv> V \<noteq> {} \<and> E \<subseteq> V\<times>V \<and> (\<forall>v\<in>V. \<forall>v'\<in>V. (v,v') \<in> E\<^sup>*)"

(** An empty graph is not strongly connected. *)
lemma strongly_connected_notempty[simp]:
  "\<not>strongly_connected E {}"
  unfolding strongly_connected_def by blast

(** The edges in a strongly connected graph must include all vertices in V. *)
lemma strongly_connected_E_in_V: "strongly_connected E V \<Longrightarrow> E \<subseteq> V\<times>V"
  unfolding strongly_connected_def by blast

(** If a graph is strongly connected, there exists a path from every node to every other node. *)
lemma strongly_connected_path: "strongly_connected E V \<Longrightarrow> \<forall>v\<in>V. \<forall>v'\<in>V. \<exists>vs. path E v vs v'"
  unfolding strongly_connected_def
  using rtrancl_is_path[of _ _ E] by simp

context finite_graph_V
begin
section\<open>Strongly Connected Graphs Restricted to a Region\<close>

(** If a subgraph is strongly connected, then the regular graph restricted to that subgraph
    is also already strongly connected. *)
lemma strongly_connected_restr_subgraph:
  "\<lbrakk>E' \<subseteq> E; V' \<subseteq> V; strongly_connected E' V'\<rbrakk> \<Longrightarrow> strongly_connected (E\<inter>E') (V\<inter>V')"
  unfolding strongly_connected_def
  using E_in_V by (auto simp: Int_absorb1)

(** If a restricted graph is strongly connected, then there exists a path from every node in the
    region to every other node in the region. *)
lemma strongly_connected_restr_connected:
  "\<lbrakk>R \<subseteq> V; strongly_connected (Restr E R) (V\<inter>R)\<rbrakk> \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. (v,v')\<in>(Restr E R)\<^sup>*"
  unfolding strongly_connected_def by blast

(** If a restricted graph is strongly connected, then there always exists a path between
    each pair of nodes in that region. *)
lemma strongly_connected_restr_path:
  "\<lbrakk>R \<subseteq> V; strongly_connected (Restr E R) (V\<inter>R)\<rbrakk> \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  using strongly_connected_restr_connected[of R] path_iff_rtrancl[of _ _ "Restr E R"] by blast


section \<open>Strongly Connected Components\<close>
(** A component in a graph is strongly connected when the graph restricted to that component is
    strongly connected and maximal; there is no larger component that contains it and is also
    strongly connected. *)
definition SCC :: "'v set \<Rightarrow> bool" where
  "SCC R \<equiv> R \<subseteq> V \<and> strongly_connected (Restr E R) (V\<inter>R) \<and>
    (\<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') (V\<inter>R'))"

(** SCCs are non-empty because our strong connectivity definition excludes empty graphs. *)
lemma SCC_notempty[simp]: "\<not>SCC {}"
  unfolding SCC_def by fastforce

(** All strongly connected components are subsets of V. *)
lemma SCC_in_V: "SCC R \<Longrightarrow> R \<subseteq> V"
  unfolding SCC_def by simp

(** Strongly connected components are finite sets. *)
lemma SCC_finite: "SCC R \<Longrightarrow> finite R"
  using finite_subset[OF SCC_in_V fin_V] .

(** The graph restricted to a strongly connected component is strongly connected. *)
lemma SCC_strongly_connected: "SCC R \<Longrightarrow> strongly_connected (Restr E R) (V\<inter>R)"
  unfolding SCC_def by blast

(** Strongly connected components are maximal. *)
lemma SCC_maximal: "SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') (V\<inter>R')"
  unfolding SCC_def by blast

(** There are a finite number of SCCs in every graph. *)
lemma finite_SCCs: "finite {R. SCC R}"
  unfolding SCC_def by fast

(** For every pair of nodes in a strongly connected component, there exists a path from one to the
    other. *)
lemma SCC_path: "SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  unfolding SCC_def using strongly_connected_restr_path by simp


section \<open>Bottom Strongly Connected Components\<close>
(** A bottom SCC is a strongly connected component where there exist no edges from the SCC to the
    region outside of it; the SCC is closed. *)
definition bottom_SCC :: "'v set \<Rightarrow> bool" where
  "bottom_SCC R \<equiv> SCC R \<and> E `` R \<subseteq> R"

(** Bottom SCCs are strongly connected components. *)
lemma bottom_SCC_is_SCC: "bottom_SCC R \<Longrightarrow> SCC R"
  unfolding bottom_SCC_def by simp

(** Bottom SCCs are not empty because strongly connected components are not empty by our definition *)
lemma bottom_SCC_notempty[simp]: "\<not>bottom_SCC {}"
  using bottom_SCC_is_SCC by force

(** Bottom SCCs exist within the graph. *)
lemma bottom_SCC_in_V: "bottom_SCC R \<Longrightarrow> R \<subseteq> V"
  using SCC_in_V[OF bottom_SCC_is_SCC] .

(** Bottom SCCs are finite. *)
lemma bottom_SCC_finite: "bottom_SCC R \<Longrightarrow> finite R"
  using finite_subset[OF bottom_SCC_in_V fin_V] .

(** The graph restricted to a bottom SCC is strongly connected. *)
lemma bottom_SCC_strongly_connected: "bottom_SCC R \<Longrightarrow> strongly_connected (Restr E R) (V\<inter>R)"
  using SCC_strongly_connected[OF bottom_SCC_is_SCC] .

(** All bottom SCCs are maximal. *)
lemma bottom_SCC_maximal: "bottom_SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') (V\<inter>R')"
  using SCC_maximal[OF bottom_SCC_is_SCC] .

(** Bottom SCCs are closed in E. *)
lemma bottom_SCC_closed: "bottom_SCC R \<Longrightarrow> E `` R \<subseteq> R"
  unfolding bottom_SCC_def by simp

(** There are a finite number of bottom SCCs in the graph. *)
lemma finite_bottom_SCCs:
  "finite {R. bottom_SCC R}"
  using finite_subset[OF Collect_mono finite_SCCs] bottom_SCC_is_SCC by blast

(** For every pair of nodes in a strongly connected component, there exists a path from one to the
    other. *)
lemma bottom_SCC_path: "bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  using SCC_path[OF bottom_SCC_is_SCC] by blast


section \<open>Non-trivial Bottom SCCs\<close>
(** Non-trivial bottom SCCs are those that contain at least one edge within them. *)
definition nt_bottom_SCC :: "'v set \<Rightarrow> bool" where
  "nt_bottom_SCC R \<equiv> bottom_SCC R \<and> (Restr E R) \<noteq> {}"

(** A non-trivial bottom SCC is a bottom SCC. *)
lemma nt_bottom_SCC_is_bottom_SCC: "nt_bottom_SCC R \<Longrightarrow> bottom_SCC R"
  unfolding nt_bottom_SCC_def by simp

(** A non-trivial bottom SCC is a strongly connected component. *)
lemma nt_bottom_SCC_is_SCC: "nt_bottom_SCC R \<Longrightarrow> SCC R"
  using bottom_SCC_is_SCC[OF nt_bottom_SCC_is_bottom_SCC] .

(** A non-trivial bottom SCC is not empty. *)
lemma nt_bottom_SCC_notempty[simp]: "\<not>nt_bottom_SCC {}"
  using nt_bottom_SCC_is_bottom_SCC by force

(** A non-trivial bottom SCC exists within the graph. *)
lemma nt_bottom_SCC_in_V: "nt_bottom_SCC R \<Longrightarrow> R \<subseteq> V"
  using SCC_in_V[OF nt_bottom_SCC_is_SCC] .

(** Non-trivial bottom SCCs are finite. *)
lemma nt_bottom_SCC_finite: "nt_bottom_SCC R \<Longrightarrow> finite R"
  using finite_subset[OF nt_bottom_SCC_in_V fin_V] .

(** The graph restricted to a non-trivial bottom SCC is strongly connected. *)
lemma nt_bottom_SCC_strongly_connected: "nt_bottom_SCC R \<Longrightarrow> strongly_connected (Restr E R) (V\<inter>R)"
  using SCC_strongly_connected[OF nt_bottom_SCC_is_SCC] .

(** Non-trivial bottom SCCs are maximal. *)
lemma nt_bottom_SCC_maximal:
  "nt_bottom_SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') (V\<inter>R')"
  using SCC_maximal[OF nt_bottom_SCC_is_SCC] .

(** A non-trivial bottom SCC has at least one edge. *)
lemma nt_bottom_SCC_has_edge: "nt_bottom_SCC R \<Longrightarrow> (Restr E R) \<noteq> {}"
  unfolding nt_bottom_SCC_def by blast

(** Non-trivial bottom SCCs cannot consist of a single node without a self-loop. *)
lemma nt_bottom_SCC_nontrivial: "(v,v) \<notin> E \<Longrightarrow> \<not>nt_bottom_SCC {v}"
  unfolding nt_bottom_SCC_def by fast

(** A non-trivial bottom SCC is closed. *)
lemma nt_bottom_SCC_closed: "nt_bottom_SCC R \<Longrightarrow> E `` R \<subseteq> R"
  using bottom_SCC_closed[OF nt_bottom_SCC_is_bottom_SCC] .

(** There are a finite number of non-trivial bottom SCCs in the graph. *)
lemma finite_nt_bottom_SCCs:
  "finite {R. nt_bottom_SCC R}"
  using finite_subset[OF Collect_mono finite_bottom_SCCs] nt_bottom_SCC_is_bottom_SCC by blast

(** For every pair of nodes in a non-trivial bottom SCC, there exists a path from one node to the
    other. *)
lemma nt_bottom_SCC_path: "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  using SCC_path[OF nt_bottom_SCC_is_SCC] .

(** In a non-trivial bottom SCC, every node in the SCC has a successor that also exists in the SCC. *)
lemma nt_bottom_SCC_succ_in_SCC:
  "\<lbrakk>nt_bottom_SCC R; v\<in>R\<rbrakk> \<Longrightarrow> \<exists>v'\<in>R. (v,v')\<in>E"
proof -
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v \<in> R"
  from SCC_R have R_in_V: "R \<subseteq> V"
    using nt_bottom_SCC_in_V by auto
  consider (loop) "(v,v) \<in> E" | (no_loop) "(v,v) \<notin> E" by blast
  thus "\<exists>v'\<in>R. (v,v') \<in> E" proof cases
    (** If there is a self loop, the successor of v in R is v itself. *)
    case loop with v_in_R show ?thesis by fast
  next
    case no_loop
    (** Because the bottom SCC is non-trivial, without a self loop from v, there  must exist another
        node v' in R that is not v. *)
    from nt_bottom_SCC_nontrivial[OF this] SCC_R have "R\<noteq>{v}" by auto
    with v_in_R  obtain v' where
      v'_in_R: "v' \<in> R" and v'_not_v: "v' \<noteq> v"
      by blast
    (** Because the component is strongly connected, we can obtain a path from v to v',  which is
        not empty because v and v' are not the same node. *)
    from nt_bottom_SCC_path[OF SCC_R] v_in_R v'_in_R v'_not_v obtain vs where
      restr_path_v_vs_v': "path (Restr E R) v vs v'" and
      vs_notempty: "vs \<noteq> []"
      by force
    (** This path exists in the whole graph, but all nodes within it are nodes in R. *)
    from restr_V_path[OF this] have
      vs_in_R: "set vs \<subseteq> R" and path_v_vs_v': "path E v vs v'" by blast+
    (** Now we can get the next node w in the path from v to v'. *)
    with v'_in_R obtain w ws where
      ws_in_vs: "vs = v#ws" and w_succ_v: "(v,w) \<in> E" and path_w_ws_v': "path E w ws v'"
      using path_D[OF path_v_vs_v' vs_notempty] by blast
    (** This node is in R because the whole path is in R.  *)
    with v'_in_R vs_in_R have w_in_R: "w\<in>R"
      using origin_in_path[OF path_w_ws_v'] by fastforce
    (** Now we can use w as the successor of v in R. *)
    with w_succ_v show ?thesis by blast
  qed
qed

(** For every pair of nodes in a non-trivial bottom SCC, there exists a non-empty path from one node
    to the other.  *)
lemma nt_bottom_SCC_path_nonempty:
  "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. vs \<noteq> [] \<and> path (Restr E R) v vs v'"
proof (intro ballI)
  fix v v'
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v \<in> R" and v'_in_R: "v' \<in> R"
  from SCC_R have R_in_V: "R \<subseteq> V" and R_connected: "strongly_connected (Restr E R) (V\<inter>R)"
    using nt_bottom_SCC_in_V nt_bottom_SCC_strongly_connected by blast+
  (** Because R is strongly connected, we know there is a path from v to v' in the reflexive
      transitive closure of E restricted to R. We can use an induction over this to show our thesis. *)
  from strongly_connected_restr_connected[OF this] v_in_R v'_in_R
  have "(v,v') \<in> (Restr E R)\<^sup>*" by blast
  thus "\<exists>vs. vs \<noteq> [] \<and> path (Restr E R) v vs v'"
  proof (induction rule: converse_rtrancl_induct)
    case base
    (** We know that in a restricted subgraph that is strongly connected, each node has a successor
        in the restricted region. We take this successor and get the path from v' to w, which only
        consists of v' itself. *)
    from nt_bottom_SCC_succ_in_SCC[OF SCC_R v'_in_R]
    obtain w where w_in_R: "w \<in> R" and w_succ_v': "(v',w)\<in>E" by blast
    hence path_v_w: "path E v' [v'] w" by simp
    (** Now we get the (possibly empty) path from w back to v'. We prepend v', completing the loop. *)
    from nt_bottom_SCC_path[OF SCC_R] w_in_R v'_in_R obtain vs where
      path_w_vs_v': "path (Restr E R) w vs v'" by fast
    with w_succ_v' v'_in_R w_in_R have "path (Restr E R) v' (v'#vs) v'" by auto
    thus ?case by blast
  next
    (** In the step case, we already have a non-empty path between two nodes, and a predecessor of
        the start of that path. We just prepend the predecessor to complete the path from there to
        the destination. *)
    case (step y z) thus ?case by fastforce
  qed
qed

(** From every node in a non-trivial bottom SCC, there exists a cycle. *)
lemma nt_bottom_SCC_cycle: "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<exists>ys. cycle (Restr E R) v ys"
proof (rule ballI)
  fix v
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v\<in>R"
  (** We can take some other (not necessarily different) v' in R and get the non-empty path from
      v to v', append the path from v' to v, and we have a cycle. *)
  then obtain v' where v'_in_R: "v'\<in>R" by blast
  from nt_bottom_SCC_path_nonempty[OF SCC_R] v_in_R v'_in_R
  obtain vs1 vs2 where
    path_v_v': "path (Restr E R) v vs1 v'" and vs1_notempty: "vs1 \<noteq> []" and
    path_v'_v: "path (Restr E R) v' vs2 v" and vs2_notempty: "vs2 \<noteq> []"
    by blast
  hence "path (Restr E R) v (vs1@vs2) v" by auto
  with vs1_notempty vs2_notempty show "\<exists>ys. cycle (Restr E R) v ys"
    unfolding cycle_def by blast
qed
end (** End of context finite_graph_V *)

end