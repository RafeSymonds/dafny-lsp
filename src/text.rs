use tower_lsp::lsp_types::Position;

/// How the client counts columns. LSP defaults to UTF-16; clients can opt into UTF-8.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    Utf8,
    Utf16,
}

/// Byte offsets of line starts, used to convert between byte offsets and LSP positions.
#[derive(Clone, Debug)]
pub struct LineIndex {
    starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> Self {
        let mut starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                starts.push(i + 1);
            }
        }
        LineIndex { starts }
    }

    pub fn line_count(&self) -> usize {
        self.starts.len()
    }

    pub fn line_start(&self, line: usize) -> usize {
        self.starts[line.min(self.starts.len() - 1)]
    }

    /// End of the line's content, not counting the line break.
    pub fn line_end(&self, text: &str, line: usize) -> usize {
        let mut end = if line + 1 < self.starts.len() {
            self.starts[line + 1] - 1
        } else {
            text.len()
        };
        let start = self.line_start(line);
        if end > start && text.as_bytes()[end - 1] == b'\r' {
            end -= 1;
        }
        end
    }

    pub fn line_of(&self, offset: usize) -> usize {
        match self.starts.binary_search(&offset) {
            Ok(line) => line,
            Err(line) => line - 1,
        }
    }

    pub fn offset(&self, text: &str, pos: Position, enc: Encoding) -> usize {
        let line = pos.line as usize;
        if line >= self.starts.len() {
            return text.len();
        }
        let start = self.starts[line];
        let end = self.line_end(text, line);
        start + column_to_byte(&text[start..end], pos.character as usize, enc)
    }

    pub fn position(&self, text: &str, offset: usize, enc: Encoding) -> Position {
        let mut offset = offset.min(text.len());
        while !text.is_char_boundary(offset) {
            offset -= 1;
        }
        let line = self.line_of(offset);
        let start = self.starts[line];
        let col = match enc {
            Encoding::Utf8 => offset - start,
            Encoding::Utf16 => text[start..offset].encode_utf16().count(),
        };
        Position::new(line as u32, col as u32)
    }

    pub fn point(&self, offset: usize) -> tree_sitter::Point {
        let line = self.line_of(offset);
        tree_sitter::Point::new(line, offset - self.starts[line])
    }
}

pub fn column_to_byte(line: &str, col: usize, enc: Encoding) -> usize {
    match enc {
        Encoding::Utf8 => {
            let mut c = col.min(line.len());
            while !line.is_char_boundary(c) {
                c -= 1;
            }
            c
        }
        Encoding::Utf16 => {
            let mut units = 0;
            for (i, ch) in line.char_indices() {
                if units >= col {
                    return i;
                }
                units += ch.len_utf16();
            }
            line.len()
        }
    }
}

pub fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '?' || c == '\''
}

pub fn is_valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c.is_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(is_ident_char) && !crate::syntax::KEYWORDS.contains(&name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_columns() {
        let text = "a\nxé𝄞b\n";
        let idx = LineIndex::new(text);
        // 'b' is after x (1 unit), é (1 unit), 𝄞 (2 units)
        let off = idx.offset(text, Position::new(1, 4), Encoding::Utf16);
        assert_eq!(&text[off..off + 1], "b");
        assert_eq!(idx.position(text, off, Encoding::Utf16), Position::new(1, 4));
        assert_eq!(idx.position(text, off, Encoding::Utf8), Position::new(1, 7));
    }

    #[test]
    fn clamps_past_line_end() {
        let text = "ab\r\ncd";
        let idx = LineIndex::new(text);
        assert_eq!(idx.offset(text, Position::new(0, 10), Encoding::Utf16), 2);
        assert_eq!(idx.offset(text, Position::new(5, 0), Encoding::Utf16), text.len());
    }
}
