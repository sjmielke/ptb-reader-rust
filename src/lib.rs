#[macro_use]
extern crate pest;
use pest::prelude::*;

extern crate glob;
use glob::glob;

extern crate simple_error;
use simple_error::SimpleError;

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

impl PTBTree {
    /// Return bracketed (but not outside-bracketed!) PTB notation.
    fn render_simple_brackets(&self) -> String {
        match *self {
            PTBTree::InnerNode { ref label, ref children } => {
                format!("({} {})", label, children.iter().map(|c| c.render_simple_brackets()).collect::<Vec<_>>().join(" "))
            }
            PTBTree::TerminalNode { ref label } => {
                label.to_string()
            }
        }
    }
    
    /// Return bracketed (and outside-bracketed!) PTB notation:
    ///
    /// ```rust
    /// use ptb_reader::PTBTree;
    /// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
    /// assert_eq!(tree.render(), "((NT t))")
    /// ```
    pub fn render(&self) -> String {
        format!("({})", self.render_simple_brackets())
    }
    
    /// Return `String` from joined terminals at the leaves (i.e, *front*, *yield*).
    /// 
    /// ```rust
    /// use ptb_reader::PTBTree;
    /// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
    /// assert_eq!(tree.front(), "t")
    /// ```
    pub fn front(&self) -> String {
        match *self {
            PTBTree::TerminalNode { ref label } => label.clone(),
            PTBTree::InnerNode { ref children, .. } => {
                children.iter().map(|c| c.front()).collect::<Vec<String>>().join(" ")
            }
        }
    }
    
    /// Return `String` from joined pre-terminals (i.e., POS tags).
    /// 
    /// ```rust
    /// use ptb_reader::PTBTree;
    /// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
    /// assert_eq!(tree.pos_front(), "NT")
    /// ```
    pub fn pos_front(&self) -> String {
        match *self {
            PTBTree::TerminalNode { .. } => panic!("Encountered unexpected terminal while getting the POS front!"),
            PTBTree::InnerNode { ref children, ref label } => {
                //if let [PTBTree::TerminalNode { label } ] = children {
                if children.len() == 1 {
                    if let PTBTree::TerminalNode { .. } = children[0] {
                        return label.clone()
                    }
                }
                
                children.iter().map(|c| c.pos_front()).collect::<Vec<String>>().join(" ")
            }
        }
    }
    
    /// Return number of terminal words, i.e. length of front.
    pub fn front_length(&self) -> usize {
        match *self {
            PTBTree::TerminalNode { .. } => 1,
            PTBTree::InnerNode { ref children, .. } => {
                children.iter().map(|c| c.front_length()).sum()
            }
        }
    }
    
    /// Remove predicate-argument annotations and trace elements.
    /// See <http://dx.doi.org/10.3115/1075812.1075835 The Penn Treebank: annotating predicate argument structure>.
    /// Thanks to Toni Dietze for formalizing the necessary stripping :)
    pub fn strip_all_predicate_annotations(&mut self) {
        match *self {
            PTBTree::InnerNode { ref mut label, ref mut children } => {
                // Iterate suffix removal
                fn strip_one_label_suffix(s: &mut String) -> bool {
                    // Any of these in-/suffixes shall be removed from inner nodes (e.g., NNP-NOM-SBJ => NNP).
                    let functional_suffixes = ["-HLN", "-LST", "-TTL", "-CLF", "-NOM", "-ADV", "-LGS", "-PRD", "-SBJ", "-TPC", "-CLR", "-VOC", "-DIR", "-LOC", "-MNR", "-PRP", "-TMP"];
                    if let Some((i, _)) = s.char_indices().rev().nth(3) {
                        if functional_suffixes.contains(&&s[i..]) {
                            s.truncate(i);
                            return true
                        }
                    }
                    
                    // Any dash-prefixed or equals-prefixed numbers shall be removed from inner nodes (e.g., NNP-1-12 => NNP).
                    let mut gotdigit = false;
                    let mut truncation_index = None;
                    for (i, c) in s.char_indices().rev() {
                        if c.is_digit(10) {
                            gotdigit = true
                        } else if (c == '-' || c == '=') && gotdigit {
                            truncation_index = Some(i);
                            break
                        } else {
                            return false
                        }
                    }
                    match truncation_index {
                        None => false,
                        Some(i) => {s.truncate(i); true}
                    }
                }
                while strip_one_label_suffix(label) {}
                
                // Recurse over children
                let mut keeps_children = false;
                let mut remove_me_indices: Vec<usize> = Vec::new();
                for (i, c) in children.iter_mut().enumerate() {
                    c.strip_all_predicate_annotations();
                    let childlabel = match *c {
                        PTBTree::InnerNode { ref label, .. } | PTBTree::TerminalNode { ref label } => label
                    };
                    if !childlabel.is_empty() {
                        keeps_children = true
                    } else {
                        remove_me_indices.push(i)
                    }
                }
                
                
                // Mark inner node itself for deletion
                if !keeps_children || label == "-NONE-" {
                    *label = "".to_string();
                }
                // Remove from back to front
                else {
                    for &i in remove_me_indices.iter().rev() {
                        children.remove(i);
                    }
                }
            }
            PTBTree::TerminalNode { ref mut label } => {
                // Any of these are invalid leaves.
                let other_leafs = ["*", "*?*", "*NOT*", "*U*"];
                if other_leafs.contains(&&label[..]) {
                    *label = "".to_string();
                    return
                }
                
                // Any of these plus any digits are invalid leaves.
                for pref in ["*-", "*T*-", "*ICH*-", "*PPA*-", "*RNR*-", "*EXP*-"].into_iter() {
                    if label.starts_with(pref) {
                        let mut gotdigit = false;
                        for c in label[pref.len()..].chars() {
                            if c.is_digit(10) {
                                gotdigit = true
                            } else {
                                break
                            }
                        }
                        if gotdigit {
                            *label = "".to_string();
                            return
                        }
                    }
                }
            }
        }
    }
}

impl std::fmt::Display for PTBTree {
    /// Calls `self.render()`.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.render())
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
/// Wrapper around `parse_ptbtrees`, returns `None` if string contains not exactly one tree.
/// 
/// ```rust
/// use ptb_reader::*;
/// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
/// assert_eq!(tree, parse_ptbtree("((NT t))").unwrap())
/// ```
pub fn parse_ptbtree(s: &str) -> Option<PTBTree> {
    let parsed = match parse_ptbtrees(s) {
        None => return None,
        Some(p) => p
    };
    if parsed.len() != 1 {
        None
    } else {
        Some(parsed[0].clone())
    }
}

/// Parse a string of multiple trees.
/// 
/// Returns `None` if string contains anything unparseable.
/// 
/// ```rust
/// use ptb_reader::*;
/// let tree = PTBTree::InnerNode{ label: "NT".to_string(), children: vec![PTBTree::TerminalNode{ label: "t".to_string() }] };
/// assert_eq!(vec![tree.clone(), tree], parse_ptbtrees("((NT t)) ((NT t))").unwrap())
/// ```
pub fn parse_ptbtrees(s: &str) -> Option<Vec<PTBTree>> {
    let mut parser = myparser::Rdp::new(StringInput::new(s));
    
    if !parser.wholefile() || !parser.end() {
        None
    } else {
        Some(parser.get_all_trees())
    }
}

/// Parse a PTB file.
/// 
/// Wrapper for reading in a file and feeding it to `parse_ptbtrees`.
pub fn parse_ptb_file(f: &str) -> Option<Vec<PTBTree>> {
    let mut contents = String::new();
    match File::open(f) {
        Err(_) => None,
        Ok(mut fh) => match fh.read_to_string(&mut contents) {
            Err(_) => None,
            Ok(_) => parse_ptbtrees(&contents)
        }
    }
}

/// Parse a 1-per-line PTB file (SPMRL file format) (single-bracketed possible),
/// removing morph tags on non-terminals and replacing underscores with --- in NTs!
/// If `remove_after_dash` is set to True, it will even remove everything after a dash
/// (this is applied before the underscore-replacing, of course).
///
/// Just reads line per line, prepends '(' and appends ')' and calls `parse_ptbtrees`.
pub fn parse_spmrl_ptb_file(f: &str, singlebracketed: bool, remove_after_dash: bool) -> Result<Vec<PTBTree>, Box<std::error::Error>> {
    fn remove_morphtags(t: PTBTree, remove_after_dash: bool) -> PTBTree {
        match t {
            PTBTree::InnerNode{label,children} => {
                let newlabel = label.split("##").next().unwrap().to_string();
                let newlabel = if remove_after_dash {label.split("-").next().unwrap().to_string()} else {newlabel};
                let newlabel = newlabel.replace("_", "---");
                let newchildren = children.into_iter().map(|c| remove_morphtags(c, remove_after_dash)).collect::<Vec<_>>();
                PTBTree::InnerNode { label: newlabel, children: newchildren }
            }
            n@PTBTree::TerminalNode{..} => n
        }
    }
    
    let mut contents = String::new();
    match File::open(f)?.read_to_string(&mut contents) {
        Err(e) => Err(Box::new(e)),
        Ok(_) => {
            let lines = contents
                .split('\n')
                .filter(|s| *s != "")
                .collect::<Vec<&str>>();
            let parses: Vec<Option<PTBTree>> = if singlebracketed {
                lines.into_iter().map(|s| parse_ptbtree(&format!("({})", s))).collect()
            } else {
                lines.into_iter().map(parse_ptbtree).collect()
            };
            if parses.iter().any(|o| o.is_none()) {
                Err(Box::new(SimpleError::new("Some parses were none!")))
            } else {
                Ok(parses
                    .into_iter()
                    .map(|s| remove_morphtags(s.unwrap(), remove_after_dash))
                    .collect::<Vec<PTBTree>>())
            }
        }
    }
}

/// Parse the free PTB sample files (`wsj_0001.mrg` to `wsj_0199.mrg`).
/// 
/// Will `panic` if anything goes wrong.
/// 
/// Wrapper around `parse_ptb_file`.
pub fn parse_ptb_sample_dir(mergeddir: &str) -> Vec<PTBTree> {
    let mut result = Vec::new();
    for num in 1..200 {
        let filename = mergeddir.to_string() + &format!("wsj_{:04}.mrg", num);
        result.extend(parse_ptb_file(&filename).unwrap())
    }
    result
}

/// Parse `{mergeddir}/{section}/*.mrg` files.
/// 
/// Will `panic` if anything goes wrong.
/// 
/// Wrapper around `parse_ptb_file`.
pub fn parse_ptb_sections(mergeddir: &str, sections: Vec<usize>) -> Vec<PTBTree> {
    let mut result = Vec::new();
    for section in sections {
        //println!("Reading section {}", section);
        for entry in glob(&format!("{}/{:02}/*.mrg", mergeddir, section)).unwrap() {
            if let Ok(path) = entry {
                result.extend(parse_ptb_file(path.to_str().unwrap()).unwrap())
            }
        }
    }
    result
}

/// Parse any directory containing `*.mrg` files.
/// 
/// Will `panic` if anything goes wrong.
/// 
/// Wrapper around `parse_ptb_file`.
pub fn parse_ptb_dir(mergeddir: &str) -> Vec<PTBTree> {
    let mut result = Vec::new();
    for entry in glob(&format!("{}/**/*.mrg", mergeddir)).unwrap() {
        if let Ok(path) = entry {
            result.extend(parse_ptb_file(path.to_str().unwrap()).unwrap())
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    
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
                PTBTree::InnerNode{ label: "D".to_string(), children: vec![
                    PTBTree::TerminalNode{ label: "2".to_string() }
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
    fn front_of_ptb_tree() {
        let s: String = sample_tree().front();
        assert_eq!(s, "2 1 1 2")
    }
    
    #[test]
    fn pos_front_of_ptb_tree() {
        let s: String = sample_tree().pos_front();
        assert_eq!(s, "A B C D")
    }
    
    #[test]
    fn test_ptbtree_display() {
        let s = "((ROOT (A 2) (X (B 1) (C 1) (D 2))))";
        assert_eq!(format!("{}", sample_tree()), s)
    }
    
    #[test]
    fn test_parser() {
        let puretree = parse_ptbtree("((ROOT (A x) (C 1)))\n").unwrap();
        assert_eq!(puretree, parse_ptbtree("((ROOT (A   x)  (C  1)))\n").unwrap());
        assert_eq!(puretree, parse_ptbtree("((ROOT (A    x)  (C  1) ))\n").unwrap());
        assert_eq!(puretree, parse_ptbtree("((ROOT (A    x) \n (C \n 1) ))\n").unwrap());
        
        for t in sample_trees(4) {
            assert!(parse_ptbtree(&format!("{}\n", t)).unwrap() == t.clone());
        }
    }
    
    #[test]
    //#[ignore]
    fn parse_actual_ptb_sample() {
        let t1 = parse_ptb_sample_dir("/home/sjm/documents/Uni/FuzzySP/penn-treebank-sample/treebank/combined/");
        let t2 = parse_ptb_dir("/home/sjm/documents/Uni/FuzzySP/penn-treebank-sample/treebank/combined/");
        
        assert_eq!(3914, t1.len());
        assert_eq!(3914, t2.len());
        assert_eq!(t1, t2)
    }
    
    #[test]
    #[ignore]
    fn extract_trainset_yield() {
        for (range, name) in vec![((2..22), "2-21"), ((22..23), "22")] {
            let train_trees = parse_ptb_sections("/home/sjm/documents/Uni/FuzzySP/treebank-3_LDC99T42/treebank_3/parsed/mrg/wsj", range.collect());
            let mut yields: Vec<String> = Vec::new();
            let mut pos_yields: Vec<String> = Vec::new();
            
            for mut t in train_trees {
                t.strip_all_predicate_annotations();
                yields.push(t.front() + "\n");
                pos_yields.push(t.pos_front() + "\n")
            }
            
            let mut f = File::create(format!("/home/sjm/documents/Uni/FuzzySP/pcfg-experiments/pos-tagging/data/ptb.{}.lex", name)).expect("Unable to create file");
            for y in &yields {
                f.write_all(y.as_bytes()).expect("Unable to write data")
            }
            let mut f = File::create(format!("/home/sjm/documents/Uni/FuzzySP/pcfg-experiments/pos-tagging/data/ptb.{}.tag", name)).expect("Unable to create file");
            for y in &pos_yields {
                f.write_all(y.as_bytes()).expect("Unable to write data")
            }
        }
    }
    
    #[test]
    fn readme_example() {
        let s: &str = "((S (NNP John) (VP (VBD saw) (NNP Mary))))";
        let t: PTBTree = 
            PTBTree::InnerNode{ label: "S".to_string(), children: vec![
                PTBTree::InnerNode{ label: "NNP".to_string(), children: vec![
                    PTBTree::TerminalNode{ label: "John".to_string() }
                ] },
                PTBTree::InnerNode{ label: "VP".to_string(), children: vec![
                    PTBTree::InnerNode{ label: "VBD".to_string(), children: vec![
                        PTBTree::TerminalNode{ label: "saw".to_string() }
                    ] },
                    PTBTree::InnerNode{ label: "NNP".to_string(), children: vec![
                        PTBTree::TerminalNode{ label: "Mary".to_string() }
                    ] }
                ] }
            ] }
        ;
        assert_eq!(parse_ptbtree(s).unwrap(), t);
        assert_eq!(t.render(), s);
        assert_eq!(t.front(), "John saw Mary");
        
        let s: &str      = "((S (NNP     John) (VP            (VBD saw) (NNP Mary)              )))";
        let s_pred: &str = "((S (NNP-SBJ John) (VP (NP *T*-1) (VBD saw) (NNP Mary) (-NONE- nada))))";

        let mut t = parse_ptbtree(s_pred).unwrap();
        t.strip_all_predicate_annotations();
        assert_eq!(t, parse_ptbtree(s).unwrap())
    }
    
    #[test]
    fn test_predicate_annotations_removal() {
        // ((S
        //         (NNP-NOM-SBJ
        //             (N John)
        //             (* K.)
        //             (-NONE- nay)
        //         )
        //         (VP-PRD
        //             (VBD-12-15 verbed)
        //             (*T*-42 something)
        //         )
        //         (nuh-uh *T*-42)
        //         ($ *)
        //         (. .)
        //         (! !)
        // ))
        
        let mut full_t = parse_ptbtree("((S (NNP-NOM-SBJ (N John) (* K.) (-NONE- nay)) (VP-PRD (VBD-12-15 verbed) (*T*-42 something)) (nuh-uh *T*-42) ($ *) (. .) (! !)))").unwrap();
        let stripped_t = parse_ptbtree("((S (NNP (N John) (* K.)) (VP (VBD verbed) (*T* something)) (. .) (! !)))").unwrap();
        
        full_t.strip_all_predicate_annotations();
        
        assert_eq!(full_t, stripped_t);
    }
    
    #[test]
    #[ignore]
    fn words_in_testset() {
        let mut tokens = 0;
        let mut types: HashSet<String> = HashSet::new();
        let mut sentlengths: Vec<usize> = Vec::new();
        for mut t in parse_ptb_sections("/home/sjm/documents/Uni/FuzzySP/treebank-3_LDC99T42/treebank_3/parsed/mrg/wsj", vec![22]) {
            t.strip_all_predicate_annotations();
            let sentlen = t.front_length();
            tokens += sentlen;
            sentlengths.push(sentlen);
            for w in t.front().split(' ') {
                types.insert(w.to_string());
            }
        }
        println!("Tokens in test: {}, Types in test: {}", tokens, types.len());
        println!("Sentence lengths:");
        sentlengths.sort();
        for v in sentlengths {
            print!("{} ", v)
        }
    }
    
    #[test]
    fn parse_spmrl_ptb() {
        let lang1 = "GERMAN";
        let lang2 = "German";
        let path = format!("/home/sjm/documents/Uni/FuzzySP/spmrl-2014/data/{}_SPMRL/gold/ptb/train5k/train5k.{}.gold.ptb", lang1, lang2);
        match parse_spmrl_ptb_file(&path, true, false) {
            Err(e) => println!("\nError!\n{}", e),
            Ok(p) => println!("\nSuccess!\n{}", p[0])
        }
    }
}
