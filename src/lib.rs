#[macro_use]
extern crate pest;
use pest::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PTBTree {
    InnerNode {
        label: String,
        children: Vec<PTBTree>
    },
    TerminalNode {
        label: String
    }
}

impl std::fmt::Display for PTBTree {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            &PTBTree::InnerNode { ref label, ref children } => {
                try!(write!(f, "({} ", label));
                for (i, c) in children.iter().enumerate() {
                    try!(write!(f, "{}", c));
                    if i < children.len() - 1 {
                        try!(write!(f, " "));
                    }
                }
                write!(f, ")")
            }
            &PTBTree::TerminalNode { ref label } => {
                write!(f, "{}", label)
            }
        }
    }
}

pub fn parse_ptbtree(s: &str) -> PTBTree {
    // println!("\n\nNow parsing: {}", s);
    
    impl_rdp! {
        grammar! {
            root      =  { ["("] ~ node ~ endmarker }
            node      = _{ headed | terminal }
            headed    =  { ["("] ~ nt ~ ([" "] ~ node)+ ~ endmarker }
            endmarker =  { [")"] }
            terminal  =  { basechar+ | [")"] | ["("] }
            nt        =  { basechar+ }
            basechar  = _{ ['0'..'9'] | ['a'..'z'] | ['A'..'Z'] | ["-"] | ["_"] | [","] | ["."] }
        }
        
        process! {
            gather(&self) -> PTBTree {
                (_: root, nodes: _consume_until_endmarker()) => {
                    assert!(nodes.len() == 1);
                    nodes[0].clone()
                }
            }
            
            _consume_until_endmarker(&self) -> Vec<PTBTree> {
                (_: headed, &head: nt, mut innernodes: _consume_until_endmarker(), mut follow: _consume_until_endmarker()) => {
                    innernodes.reverse();
                    let newnode = PTBTree::InnerNode{ label: head.to_string(), children: innernodes };
                    follow.push(newnode);
                    follow
                },
                (&val: terminal, mut follow: _consume_until_endmarker()) => {
                    let newnode = PTBTree::TerminalNode{ label: val.to_string() };
                    follow.push(newnode);
                    follow
                },
                (_: endmarker) => {
                    Vec::new()
                }
            }
        }
    }
    
    let mut parser = Rdp::new(StringInput::new(s)); //reset?
    
    assert!(parser.root());
    assert!(parser.end());
    
    // println!("");
    // for tok in parser.queue() {
    //     println!("{:>10} {}", format!("{:?}", tok.rule), &s[tok.start..tok.end])
    // }
    
    parser.gather()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn sample_trees(level: usize) -> Vec<PTBTree> {
        if level == 0 {
            vec![
                PTBTree::TerminalNode { label: "0".to_string() },
                PTBTree::TerminalNode { label: "a".to_string() },
                PTBTree::TerminalNode { label: ")".to_string() },
                PTBTree::TerminalNode { label: "_".to_string() },
                PTBTree::TerminalNode { label: "(".to_string() },
            ]
        } else {
            vec![
                PTBTree::InnerNode { label: "A".to_string(), children: sample_trees(level - 1) },
                PTBTree::InnerNode { label: "B".to_string(), children: sample_trees(level - 1) },
                PTBTree::InnerNode { label: "C".to_string(), children: sample_trees(level - 1) },
            ]
        }
    }
    
    #[test]
    fn test_ptbtree_display() {
        let tree =
            PTBTree::InnerNode{ label: "ROOT".to_string(), children: vec![
                PTBTree::InnerNode{ label: "A".to_string(), children: vec![
                    PTBTree::TerminalNode{ label: "2".to_string() }
                ] },
                PTBTree::InnerNode{ label: "X".to_string(), children: vec![
                    PTBTree::InnerNode{ label: "B".to_string(), children: vec![
                        PTBTree::TerminalNode{ label: "1".to_string() }
                    ] },
                    PTBTree::InnerNode{ label: "C".to_string(), children: vec![
                        PTBTree::TerminalNode{ label: "1".to_string() }
                    ] },
                    PTBTree::TerminalNode{ label: "2".to_string() },
                    PTBTree::InnerNode{ label: "D".to_string(), children: vec![
                        PTBTree::TerminalNode{ label: "1".to_string() }
                    ] }
                ] }
            ] };
        let s = "((ROOT (A 2) (X (B 1) (C 1) 2 (D 1))))";
        assert!(format!("({})", tree) == s);
    }
    
    #[test]
    fn test_parser() {
        for t in sample_trees(3) {
            assert!(parse_ptbtree(&format!("({})", t)) == t.clone());
        }
    }
}
