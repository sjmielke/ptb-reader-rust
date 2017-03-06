#[macro_use]
extern crate pest;
use pest::prelude::*;

use std::fs::File;
use std::io::prelude::*;

/// Arbitrarily wide recursive trees of `String`.
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
    /// Return bracketed PTB-like notation:
    ///
    /// ```rust
    /// use ptb_reader::PTBTree;
    /// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
    /// assert_eq!(format!("{}", tree), "(NT t)")
    /// ```
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

impl std::convert::From<PTBTree> for String {
    /// Conversion into String of terminals at the leaves (i.e, *front*, *yield*).
    ///
    /// ```rust
    /// use ptb_reader::PTBTree;
    /// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
    /// assert_eq!(String::from(tree), "t")
    /// ```
    fn from(t: PTBTree) -> String {
        match t {
            PTBTree::TerminalNode { label } => label.clone(),
            PTBTree::InnerNode { label: _, children } => {
                children.iter().map(|c| c.clone().into()).collect::<Vec<String>>().join(" ")
            }
        }
    }
}

/// Internal PTB parser, using pest
mod myparser {
    use super::PTBTree;
    use pest::prelude::*;
    
    impl_rdp! {
        grammar! {
            wholefile  =  { myws* ~ singletree+ }
            singletree =  { ["("] ~ myws* ~ node ~ myws* ~ endmarker ~ myws* }
            node       = _{ headed | terminal }
            headed     =  { ["("] ~ nt ~ (!closing ~ myws+ ~ node)+ ~ myws* ~ endmarker }
            closing    = _{ myws* ~ endmarker }
            endmarker  =  { [")"] }
            terminal   =  { basechar+ }
            nt         =  { basechar+ }
            basechar   = _{ !([" "] | ["("] | [")"]) ~ any }
            myws       = _{ [" "] | ["\n"] | ["\r"] }
        }
        
        process! {
            get_all_trees(&self) -> Vec<PTBTree> {
                (_: wholefile, mut ts: _gatherfile()) => {
                    ts.reverse();
                    ts
                }
            }
            _gatherfile(&self) -> Vec<PTBTree> {
                (_: singletree, t: _consume_until_endmarker(), mut trees: _gatherfile()) => {
                    assert!(t.len() == 1);
                    trees.push(t[0].clone());
                    trees
                },
                () => { Vec::new() },
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
}

/// Parse a single tree.
///
/// Wrapper around `parse_ptbtrees`, `panic`ing if string contains not exactly one tree.
/// 
/// ```rust
/// use ptb_reader::*;
/// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
/// assert_eq!(tree, parse_ptbtree("((NT t))"))
/// ```
pub fn parse_ptbtree(s: &str) -> PTBTree {
    let parsed = parse_ptbtrees(s);
    if parsed.len() != 1 {
        panic!("Not exactly one tree found!")
    } else {
        parsed[0].clone()
    }
}

/// Parse a string of multiple trees.
/// 
/// ```rust
/// use ptb_reader::*;
/// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
/// assert_eq!(tree, parse_ptbtree("((NT t))"))
/// ```
pub fn parse_ptbtrees(s: &str) -> Vec<PTBTree> {
    let mut parser = myparser::Rdp::new(StringInput::new(s));
    
    assert!(parser.wholefile());
    assert!(parser.end());
    
    parser.get_all_trees()
}

/// Parse a PTB file.
/// 
/// Wrapper for reading in a file and feeding it to `parse_ptbtrees`.
pub fn parse_ptb_file(f: &str) -> Vec<PTBTree> {
    let mut contents = String::new();
    File::open(f).unwrap().read_to_string(&mut contents).unwrap();
    
    parse_ptbtrees(&contents)
}

/// Parse the free PTB sample files (`wsj_0001.mrg` to `wsj_0199.mrg`).
/// 
/// Wrapper around parse_ptb_file.
pub fn parse_ptb_sample_dir(mergeddir: &str) -> Vec<PTBTree> {
    let mut result = Vec::new();
    for num in 1..200 {
        let filename = mergeddir.to_string() + &format!("wsj_{:04}.mrg", num);
        result.extend(parse_ptb_file(&filename))
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn sample_tree() -> PTBTree {
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
        ] }
    }
    
    fn sample_trees(level: usize) -> Vec<PTBTree> {
        let mut result;
        if level == 0 {
            result = Vec::new();
        } else if level == 1 {
            result = sample_trees(level - 1);
            result.push(PTBTree::TerminalNode { label: "012".to_string() });
            result.push(PTBTree::TerminalNode { label: "abc".to_string() });
            result.push(PTBTree::TerminalNode { label: "-LRB-".to_string() });
            result.push(PTBTree::TerminalNode { label: "_".to_string() });
            result.push(PTBTree::TerminalNode { label: "-RRB-".to_string() });
        } else {
            result = sample_trees(level - 1);
            result.push(PTBTree::InnerNode { label: "ABC".to_string(), children: sample_trees(level - 1) });
            result.push(PTBTree::InnerNode { label: "B".to_string(), children: sample_trees(level - 1) });
            result.push(PTBTree::InnerNode { label: "CBA".to_string(), children: sample_trees(level - 1) });
        }
        result
    }
    
    #[test]
    fn yield_of_ptb_tree() {
        let s: String = sample_tree().into();
        assert_eq!(s, "2 1 1 2 1")
    }
    
    #[test]
    fn test_ptbtree_display() {
        let s = "((ROOT (A 2) (X (B 1) (C 1) 2 (D 1))))";
        assert_eq!(format!("({})", sample_tree()), s)
    }
    
    #[test]
    fn test_parser() {
        let puretree = parse_ptbtree("((ROOT (A x) (C 1)))\n");
        assert_eq!(puretree, parse_ptbtree("((ROOT (A   x)  (C  1)))\n"));
        assert_eq!(puretree, parse_ptbtree("((ROOT (A    x)  (C  1) ))\n"));
        assert_eq!(puretree, parse_ptbtree("((ROOT (A    x) \n (C \n 1) ))\n"));
        
        for t in sample_trees(4) {
            assert!(parse_ptbtree(&format!("({})\n", t)) == t.clone());
        }
    }
    
    #[test]
    #[ignore]
    fn parse_actual_ptb_sample() {
        assert_eq!(3914, parse_ptb_sample_dir("/home/sjm/documents/Uni/penn-treebank-sample/treebank/combined/").len())
    }
}
