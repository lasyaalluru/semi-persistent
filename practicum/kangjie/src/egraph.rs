//! Bare e-graph: add, find, union, rebuild. About 200 lines.
//! Skipping rebuild after a child merge is the bug this kata exists to show.

use crate::union_find::UnionFind;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeKey {
    pub op: String,
    pub children: Vec<usize>,
    pub lit: Option<i64>,
}

#[derive(Clone, Debug)]
pub struct Node {
    pub id: usize,
    pub key: NodeKey,
    pub class: usize,
}

pub struct EGraph {
    uf: UnionFind,
    pub nodes: Vec<Node>,
    hashcons: HashMap<NodeKey, usize>,
    pub rebuild: bool,
    pub dirty_without_rebuild: bool,
}

impl EGraph {
    pub fn new(rebuild: bool) -> Self {
        Self {
            uf: UnionFind::new(),
            nodes: Vec::new(),
            hashcons: HashMap::new(),
            rebuild,
            dirty_without_rebuild: false,
        }
    }

    pub fn find(&mut self, id: usize) -> usize {
        self.uf.find(id)
    }

    fn key(&mut self, op: &str, children: &[usize], lit: Option<i64>) -> NodeKey {
        NodeKey {
            op: op.to_string(),
            children: children.iter().map(|c| self.uf.find(*c)).collect(),
            lit,
        }
    }

    pub fn add(&mut self, op: &str, children: &[usize], lit: Option<i64>) -> usize {
        let key = self.key(op, children, lit);
        if let Some(&nid) = self.hashcons.get(&key) {
            return self.uf.find(self.nodes[nid].class);
        }
        let stale = self.hashcons.keys().any(|k| k.op == op && k.lit == lit);
        if stale && !self.rebuild {
            self.dirty_without_rebuild = true;
        }
        let class = self.uf.make();
        let nid = self.nodes.len();
        self.nodes.push(Node {
            id: nid,
            key: key.clone(),
            class,
        });
        self.hashcons.insert(key, nid);
        class
    }

    pub fn union(&mut self, a: usize, b: usize) -> usize {
        let (survivor, absorbed) = self.uf.union(a, b);
        if survivor != absorbed && self.rebuild {
            self.rebuild();
        }
        survivor
    }

    pub fn rebuild(&mut self) {
        let old = std::mem::take(&mut self.hashcons);
        for (_, nid) in old {
            let mut node = self.nodes[nid].clone();
            node.key.children = node
                .key
                .children
                .iter()
                .map(|c| self.uf.find(*c))
                .collect();
            node.class = self.uf.find(node.class);
            if let Some(&other) = self.hashcons.get(&node.key) {
                let oc = self.nodes[other].class;
                self.uf.union(oc, node.class);
                self.nodes[nid] = node;
            } else {
                self.hashcons.insert(node.key.clone(), nid);
                self.nodes[nid] = node;
            }
        }
    }

    pub fn add_count(&self, op: &str) -> usize {
        self.nodes.iter().filter(|n| n.key.op == op).count()
    }
}
