# ptb-reader
Natural language processing work on syntax starts with being able to read standard corpora, such as the Penn Treebank. This crate is able to parse the merged (i.e. syntactic structure and POS tags) files of the free sample and the full PTB Wall Street Journal section.

### Data types

The output of the parser is a `Vec<PTBTree>`, `PTBTree` being defined by:
```rust
pub enum PTBTree {
    InnerNode {
        label: String,
        children: Vec<PTBTree>
    },
    TerminalNode {
        label: String
    }
}
```

`PTBTree` implements the `Display` trait, showing the PTB-bracketed notation. It also supports `From`/`Into` `String`, yielding the front of the tree (i.e., the concatenation of all terminals).

### Example usage

```rust
let all_trees: Vec<PTBTree> = ptb_reader::parse_ptb_sample_dir("/home/sjm/documents/Uni/penn-treebank-sample/treebank/combined/");
```

```rust
let s: String = "((S (NNP John) (VP (VBD saw) (NNP Mary))))";
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
assert_eq!(format!("{}", t), s);
assert_eq!(String::from(t), "John saw Mary");
```