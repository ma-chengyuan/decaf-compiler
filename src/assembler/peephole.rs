#![allow(dead_code)]
use std::collections::HashSet;

use lazy_static::lazy_static;
use regex::Regex;

use super::Assembler;

// See https://sourceware.org/binutils/docs/as/

// "A symbol is one or more characters chosen from the set of all letters (both
// upper and lower case), digits and the three characters `_.$'. On most
// machines, you can also use $ in symbol names; exceptions are noted in Machine
// Dependencies. No symbol may begin with a digit. Case is significant."
// -- https://sourceware.org/binutils/docs/as/Symbol-Intro.html
const RE_SYMBOL: &str = r"[_a-zA-Z.][_a-zA-Z0-9$.]*";
const RE_REGISTER: &str = r"%[a-zA-Z0-9]+";
// All condition codes
const RE_CC: &str = r"a|ae|b|be|c|cxz|ecxz|rcxz|e|g|ge|l|le|na|nae|nb|nbe|nc|ne|ng|nge|nl|nle|no|np|ns|nz|o|p|pe|po|s|z";

lazy_static! {
    static ref RE_DIRECTIVE: Regex = Regex::new(r"^\s*\.[a-zA-Z0-9]+\s").unwrap();
    static ref RE_LOC: Regex = Regex::new(r"^\s*\.loc\s").unwrap();
    static ref RE_LABEL: Regex = Regex::new(&format!(r"^\s*(?<label>{}):", RE_SYMBOL)).unwrap();
    static ref RE_JMP: Regex = Regex::new(&format!(r"^\s*jmp\s+(?<label>{})", RE_SYMBOL)).unwrap();
    static ref RE_JCC_COMPARE: Regex = Regex::new(&format!(
        r"^\s*(?<jcc>je|jne|jl|jle|jg|jge)\s+(?<label>{})",
        RE_SYMBOL
    ))
    .unwrap();
    static ref RE_MOVQ: Regex = Regex::new(&format!(
        r"^\s*movq\s+(?<src>{}),\s*(?<dst>{})",
        RE_REGISTER, RE_REGISTER
    ))
    .unwrap();
    static ref RE_MOVQ_ZERO: Regex = Regex::new(&format!(
        r"^\s*(?<inst>movq\s+\$0,\s*(?<dst>{}))",
        RE_REGISTER
    ))
    .unwrap();
}

fn is_comment(line: &str) -> bool {
    line.trim_start().starts_with('#')
}

fn is_directive(line: &str) -> bool {
    RE_DIRECTIVE.is_match(line)
}

fn is_loc_directive(line: &str) -> bool {
    RE_LOC.is_match(line)
}

fn get_label(line: &str) -> Option<&str> {
    RE_LABEL
        .captures(line)
        .map(|cap| cap.name("label").unwrap().as_str())
}

fn get_jmp_label(line: &str) -> Option<&str> {
    RE_JMP
        .captures(line)
        .map(|cap| cap.name("label").unwrap().as_str())
}

fn remove_by_index<T>(vec: &mut Vec<T>, removed: &HashSet<usize>) {
    let mut i = 0;
    vec.retain(|_| {
        let retain = !removed.contains(&i);
        i += 1;
        retain
    });
}

impl Assembler {
    /// Removes jmps to the next instruction, e.g,:
    /// ```asm
    ///    jmp label
    /// label:
    /// ```
    pub(super) fn remove_unnecessary_jmps(&mut self) {
        let mut removed: HashSet<usize> = HashSet::new();
        for i in 0..self.code.len() {
            let Some(jmp_label) = get_jmp_label(&self.code[i]) else {
                continue;
            };
            for j in i + 1..self.code.len() {
                let line = &self.code[j];
                if is_comment(line) || is_directive(line) {
                    continue;
                }
                match get_label(line) {
                    Some(label) if label == jmp_label => {
                        // println!("Removing jmp to next instruction: {}", jmp_label);
                        removed.insert(i);
                        break;
                    }
                    Some(_) => continue,
                    _ => break,
                }
            }
        }
        remove_by_index(&mut self.code, &removed);
    }

    /// Replaces label a with label b in the following case:
    /// ```asm
    /// label_a:
    ///   jmp label_b
    /// ```
    pub(super) fn remove_unnecessary_labels(&mut self) {
        // This is O(n^2) for now. O(n) is possible (I guess) but it's more
        // tedious.
        loop {
            let mut replacing: Option<(usize, String, String)> = None;
            'outer: for i in 0..self.code.len() {
                let Some(label) = get_label(&self.code[i]) else {
                    continue;
                };
                for j in i + 1..self.code.len() {
                    let line = &self.code[j];
                    if is_comment(line) || is_directive(line) || get_label(line).is_some() {
                        continue;
                    }
                    match get_jmp_label(line) {
                        Some(jmp_label) if jmp_label != label => {
                            replacing = Some((i, label.to_string(), jmp_label.to_string()));
                            break 'outer;
                        }
                        _ => break,
                    }
                }
            }
            let Some((idx, label_a, label_b)) = replacing else {
                break;
            };
            // println!("Replacing {} with {}", label_a, label_b);
            self.code.remove(idx);
            let replacer = Regex::new(&format!(
                r"^(?<prec>\s*(j(mp|{})\s+)|call){}(?<succ>[^_a-zA-Z0-9$.]|$)",
                RE_CC,
                label_a.replace('.', r"\.") // Escape dots
            ))
            .unwrap();
            let replacement = format!("${{prec}}{}${{succ}}", label_b);
            for line in self.code.iter_mut() {
                *line = replacer.replace(line, &replacement).to_string();
            }
        }
    }

    /// Removes everything after a jmp up to the next label, e.g.:
    /// ```asm
    ///   jmp label
    ///   mov %rax, %rbx # Unreachable!
    /// ```
    pub(super) fn remove_unreachable_code(&mut self) {
        let mut removed = HashSet::new();
        for i in 0..self.code.len() {
            let line = &self.code[i];
            if is_comment(line) || is_directive(line) {
                continue;
            }
            if get_jmp_label(line).is_some() {
                for j in i + 1..self.code.len() {
                    let line = &self.code[j];
                    if get_label(line).is_some() {
                        break; // Stop at label
                    }
                    if is_directive(line) {
                        continue; // Do not remove directives
                    }
                    removed.insert(j);
                }
            }
        }
        remove_by_index(&mut self.code, &removed);
    }

    /// Adjust the order of cmp and jmp instructions, e.g.:
    /// ```asm
    ///   cmpq ...
    ///   jl label_a
    ///   jmp label_b
    /// label_a:
    /// ```
    /// Rewriting to
    /// ```asm
    ///   cmpq ...
    ///   jge label_b
    /// label_a
    /// ```
    /// Would save one instruction!
    pub(super) fn adjust_cmp_jmp_order(&mut self) {
        for i in 0..self.code.len() {
            let line = &self.code[i];
            if is_comment(line) || is_directive(line) {
                continue;
            }
            let Some(capture) = RE_JCC_COMPARE.captures(line) else {
                continue;
            };
            let jcc = capture.name("jcc").unwrap();
            let label_a = capture.name("label").unwrap();
            for j in i + 1..self.code.len() {
                let line = &self.code[j];
                if is_comment(line) || is_directive(line) {
                    continue;
                }
                let Some(label_b) = RE_JMP.captures(line) else {
                    break;
                };
                for k in j + 1..self.code.len() {
                    let line = &self.code[k];
                    if is_comment(line) || is_directive(line) {
                        continue;
                    }
                    match get_label(line) {
                        Some(label) if label == label_a.as_str() => {
                            let inv_jcc = match jcc.as_str() {
                                "je" => "jne",
                                "jne" => "je",
                                "jl" => "jge",
                                "jle" => "jg",
                                "jg" => "jle",
                                "jge" => "jl",
                                _ => unreachable!(),
                            };
                            let label_a_range = label_a.range();
                            let jcc_range = jcc.range();
                            let label_b = label_b.name("label").unwrap();
                            let label_b_string = label_b.as_str().to_string();
                            let label_b_range = label_b.range();
                            let label_a_string = label_a.as_str().to_string();
                            // Order matters here. label_a comes after
                            // jcc, so replacing it does not invalidate jcc'range.
                            self.code[i].replace_range(label_a_range, &label_b_string);
                            self.code[i].replace_range(jcc_range, inv_jcc);
                            self.code[j].replace_range(label_b_range, &label_a_string);
                            break;
                        }
                        Some(_) => continue,
                        _ => break,
                    }
                }
                break;
            }
        }
    }

    // Remove moving registers to themselves, e.g.:
    // ```asm
    //   mov %rax, %rax
    // ```
    pub(super) fn remove_self_movs(&mut self) {
        self.code.retain(|line| {
            if let Some(mov) = RE_MOVQ.captures(line) {
                let src = mov.name("src").unwrap().as_str();
                let dst = mov.name("dst").unwrap().as_str();
                src != dst || !dst.starts_with("%r") // Moving into non-64-bit register is not a no-op.
            } else {
                true
            }
        });
    }

    pub(super) fn replace_mov_0_with_xor(&mut self) {
        for line in self.code.iter_mut() {
            if let Some(mov) = RE_MOVQ_ZERO.captures(line) {
                let dst = mov.name("dst").unwrap().as_str();
                let inst_range = mov.name("inst").unwrap().range();
                let xor = format!("xorq {}, {}", dst, dst);
                line.replace_range(inst_range, &xor);
            }
        }
    }
}

// struct PeepholeOptimizer<'a> {
//     asm: &'a mut Assembler,
// }

// impl<'a> PeepholeOptimizer<'a> {}
