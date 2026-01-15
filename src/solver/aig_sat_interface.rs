use super::aig::AigNode;
use super::cnf::{BoolLit, Cnf};
use std::collections::HashMap;

/// Adapter that converts between AigNode and BoolLit for backward compatibility
pub struct AigBitBlasterAdapter {
    aig_blaster: super::aig_bitblaster::AigBitBlaster,
    cnf: Cnf,
    // Map from AIG node raw ID to CNF variable index
    node_var_map: HashMap<i64, usize>,
}

impl AigBitBlasterAdapter {
    pub fn new() -> Self {
        Self {
            aig_blaster: super::aig_bitblaster::AigBitBlaster::new(),
            cnf: Cnf::new(),
            node_var_map: HashMap::new(),
        }
    }

    pub fn new_with_config(config: super::config::SolverConfig) -> Self {
        Self {
            aig_blaster: super::aig_bitblaster::AigBitBlaster::new_with_config(config),
            cnf: Cnf::new(),
            node_var_map: HashMap::new(),
        }
    }

    /// Convert AIG node to BoolLit, ensuring it is encoded in CNF
    fn aig_to_bool_lit(&mut self, node: &AigNode) -> BoolLit {
        let var = self.ensure_cnf_var(node);
        BoolLit(var, !node.is_negated())
    }

    /// Ensure the AIG node has a corresponding CNF variable and clauses
    fn ensure_cnf_var(&mut self, node: &AigNode) -> usize {
        let id = node.get_raw_id();
        if let Some(&var) = self.node_var_map.get(&id) {
            return var;
        }

        let var = self.cnf.new_var();
        self.node_var_map.insert(id, var);

        if id == AigNode::TRUE_ID {
            // Assert TRUE node is true
            self.cnf.add_clause(vec![BoolLit(var, true)]);
            return var;
        }

        // If it's an AND node, encode it
        // We need to look up children in the AigManager
        // Note: we need to be careful with borrowing. We can't hold reference to aig_mgr while mutating cnf if we were using split borrows,
        // but here we are calling ensure_cnf_var recursively which mutates self.
        // So we need to extract children info first.
        let children = self.aig_blaster.aig_mgr.get_children(node);

        if let Some((left, right)) = children {
            let l_var = self.ensure_cnf_var(&left);
            let r_var = self.ensure_cnf_var(&right);

            let l_lit = BoolLit(l_var, !left.is_negated());
            let r_lit = BoolLit(r_var, !right.is_negated());
            let out_lit = BoolLit(var, true);

            // out <-> l & r
            // 1. out -> l  => !out | l
            // 2. out -> r  => !out | r
            // 3. l & r -> out => !l | !r | out

            self.cnf.add_clause(vec![BoolLit(var, false), l_lit]);
            self.cnf.add_clause(vec![BoolLit(var, false), r_lit]);

            // !l | !r | out
            let not_l = BoolLit(l_lit.0, !l_lit.1);
            let not_r = BoolLit(r_lit.0, !r_lit.1);
            self.cnf.add_clause(vec![not_l, not_r, out_lit]);
        }

        var
    }

    /// Convert BoolLit to AIG node (for constants)
    fn bool_lit_to_aig(&mut self, lit: BoolLit) -> AigNode {
        if lit.1 {
            self.aig_blaster.const_lit(true)
        } else {
            self.aig_blaster.const_lit(false)
        }
    }

    pub fn new_bool(&mut self) -> BoolLit {
        let aig_node = self.aig_blaster.new_bool();
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn mk_not(&mut self, a: BoolLit) -> BoolLit {
        let aig_a = self.bool_lit_to_aig(a);
        let result = self.aig_blaster.mk_not(&aig_a);
        self.aig_to_bool_lit(&result)
    }

    pub fn mk_and(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() {
            return self.aig_blaster.const_lit(true).into();
        }
        if lits.len() == 1 {
            return lits[0];
        }

        let aig_lits: Vec<AigNode> = lits.iter().map(|lit| self.bool_lit_to_aig(*lit)).collect();
        let mut result = aig_lits[0].clone();
        for lit in &aig_lits[1..] {
            result = self.aig_blaster.mk_and(&result, lit);
        }
        self.aig_to_bool_lit(&result)
    }

    pub fn mk_or(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() {
            return self.aig_blaster.const_lit(false).into();
        }
        if lits.len() == 1 {
            return lits[0];
        }

        let aig_lits: Vec<AigNode> = lits.iter().map(|lit| self.bool_lit_to_aig(*lit)).collect();
        let mut result = aig_lits[0].clone();
        for lit in &aig_lits[1..] {
            result = self.aig_blaster.mk_or(&result, lit);
        }
        self.aig_to_bool_lit(&result)
    }

    pub fn encode_xor_var(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        let aig_a = self.bool_lit_to_aig(a);
        let aig_b = self.bool_lit_to_aig(b);
        let result = self.aig_blaster.mk_xor(&aig_a, &aig_b);
        self.aig_to_bool_lit(&result)
    }

    pub fn get_bool_sym<S: Into<String>>(&mut self, name: S) -> BoolLit {
        let aig_node = self.aig_blaster.get_bool_sym(name);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn lookup_bool_sym(&self, name: &str) -> Option<BoolLit> {
        self.aig_blaster.lookup_bool_sym(name).map(|_node| {
            // This is a bit tricky since we need to convert without mutable access
            // For now, return a placeholder
            BoolLit(0, true)
        })
    }

    pub fn const_lit(&mut self, value: bool) -> BoolLit {
        let aig_node = self.aig_blaster.const_lit(value);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn assert_true(&mut self, lit: BoolLit) {
        self.cnf.add_clause(vec![lit]);
    }

    pub fn mk_implies(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        // a -> b is (¬a ∨ b)
        let not_a = self.mk_not(a);
        self.mk_or(&[not_a, b])
    }

    pub fn emit_bit(&mut self, t: &super::bv::BvTerm, i: u32) -> BoolLit {
        let aig_node = self.aig_blaster.emit_bit(t, i);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn bool_eq(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.bool_eq(a, b);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn emit_ult_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_ult_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn emit_ule_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_ule_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn emit_slt_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_slt_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }

    pub fn ite_bit(&mut self, c: BoolLit, t: BoolLit, e: BoolLit) -> BoolLit {
        let aig_c = self.bool_lit_to_aig(c);
        let aig_t = self.bool_lit_to_aig(t);
        let aig_e = self.bool_lit_to_aig(e);
        let result = self.aig_blaster.ite_bit(&aig_c, &aig_t, &aig_e);
        self.aig_to_bool_lit(&result)
    }

    pub fn emit_bits(&mut self, t: &super::bv::BvTerm) -> Vec<BoolLit> {
        let aig_bits = self.aig_blaster.emit_bits(t);
        aig_bits
            .into_iter()
            .map(|node| self.aig_to_bool_lit(&node))
            .collect()
    }

    // Access to underlying CNF and AIG structures
    pub fn cnf(&self) -> &Cnf {
        &self.cnf
    }

    pub fn cnf_mut(&mut self) -> &mut Cnf {
        &mut self.cnf
    }

    pub fn bool_syms(&self) -> &HashMap<String, AigNode> {
        &self.aig_blaster.bool_syms
    }

    pub fn var_bits(&self) -> &HashMap<(String, u32), AigNode> {
        &self.aig_blaster.var_bits
    }

    /// Convert AIG to CNF
    pub fn emit_cnf(&mut self) {
        self.aig_blaster.emit_cnf();
    }
}

impl Default for AigBitBlasterAdapter {
    fn default() -> Self {
        Self::new()
    }
}

// Conversion from AigNode to BoolLit (simplified)
impl From<AigNode> for BoolLit {
    fn from(_node: AigNode) -> Self {
        // This is a placeholder - in practice, we'd need proper variable mapping
        BoolLit(0, true)
    }
}
