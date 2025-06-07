/// Line break information for a file.
/// Recorded as an array of offsets of the line breaks.
/// The line break itself is treated as the termina

#[derive(Eq, PartialEq, Debug, Hash, Clone)]
pub struct LineInfo {
    /// The offset of the first character of a line.
    breaks: Vec<usize>,
}

impl LineInfo {
    pub fn new() -> LineInfo {
        LineInfo { breaks: vec![0] }
    }

    pub fn from_str(text: &str) -> LineInfo {
        LineInfo::from_bytes(text.as_bytes())
    }

    pub fn from_bytes(bytes: &[u8]) -> LineInfo {
        let mut info = LineInfo::new();
        let len = bytes.len();
        let mut cursor = 0;
        while cursor < len {
            // A line break is the last character on the current line.
            // Record the next character as the first on a line.
            match bytes[cursor] {
                b'\n' => {
                    cursor = cursor + 1;
                    info.breaks.push(cursor);
                }
                b'\r' => {
                    cursor = cursor + 1;
                    if cursor < len {
                        let c = bytes[cursor];
                        if c == b'\n' {
                            cursor = cursor + 1;
                        }
                    }
                    info.breaks.push(cursor);
                }
                _ => {
                    cursor = cursor + 1;
                }
            }
        }
        info
    }

    pub fn push(&mut self, offset: usize) {
        self.breaks.push(offset);
    }

    /// The starting offset of a line, inclusive.
    pub fn line_start(&self, line: usize) -> usize {
        self.breaks[line]
    }

    /// The ending offset of a line (exclusive).
    pub fn line_end(&self, line: usize) -> usize {
        self.breaks[line + 1]
    }

    pub fn is_offset_in_line(&self, offset: usize, line: usize) -> bool {
        self.line_start(line) <= offset && offset < self.line_end(line)
    }

    pub fn line(&self, offset: usize) -> usize {
        // 0 < n. There is always at least one break at position zero.
        let len = self.breaks.len();

        // If the offset is _after_ the last line break, the offset occurs on
        // the last line. The last line has no upper-limit, so we have to treat
        // it specially.
        if self.breaks[len - 1] <= offset {
            return len - 1;
        }

        // Otherwise, search for the line who's interval contains the offset.
        // Loop until the left bound exceeds the right.
        let mut l: usize = 0;
        let mut r: usize = len - 1;
        while l <= r {
            // M is L + halfway to R.
            let m = l + ((r - l) / 2);

            // If we are before M, then slide R down to M and continue.
            if offset < self.line_start(m) {
                r = m - 1;
                continue;
            }

            // If we are after M, then slide L up to M and continue.
            if self.line_end(m) <= offset {
                l = m + 1;
                continue;
            }

            return m;
        }

        // Failure, which can never happen.
        return usize::MAX;
    }

    /// 0-Based line and column. Column reported as a byte offset.
    pub fn loc(&self, offset: usize) -> (usize, usize) {
        let line = self.line(offset);
        let column = offset - self.line_start(line);
        (line, column)
    }

    pub fn offset(&self, pos: (usize, usize)) -> usize {
        self.line_start(pos.0) + pos.1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let info = LineInfo::from_str("");
        assert_eq!(info.line(0), 0);
    }

    #[test]
    fn test_x() {
        let info = LineInfo::from_str("x");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
    }

    #[test]
    fn test_br() {
        let info = LineInfo::from_str("\n");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 1);
    }

    #[test]
    fn test_x_br() {
        let info = LineInfo::from_str("x\n");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(2), 1);
    }

    #[test]
    fn test_br_x() {
        let info = LineInfo::from_str("\nx");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 1);
        assert_eq!(info.line(2), 1);
    }

    #[test]
    fn test_br_br() {
        let info = LineInfo::from_str("\n\n");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 1);
        assert_eq!(info.line(2), 2);
        assert_eq!(info.line(3), 2);
    }

    #[test]
    fn test_x_br_x_br() {
        let info = LineInfo::from_str("x\nx\n");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(2), 1);
        assert_eq!(info.line(3), 1);
        assert_eq!(info.line(4), 2);
    }

    #[test]
    fn test_br_x_br() {
        let info = LineInfo::from_str("\nx\n");
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 1);
        assert_eq!(info.line(2), 1);
        assert_eq!(info.line(3), 2);
    }

    #[test]
    fn test_break_at_max_offset_minus_1() {
        let mut info = LineInfo::new();
        info.push(usize::MAX - 1);
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(usize::MAX - 2), 0);
        assert_eq!(info.line(usize::MAX - 1), 1);
        assert_eq!(info.line(usize::MAX), 1);
    }

    #[test]
    fn test_2_breaks_at_max_offset_minus_1() {
        let mut info = LineInfo::new();
        info.push(usize::MAX - 1);
        info.push(usize::MAX - 1);
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(usize::MAX - 2), 0);
        assert_eq!(info.line(usize::MAX - 1), 2);
        assert_eq!(info.line(usize::MAX), 2);
    }

    #[test]
    fn test_break_at_max_offset() {
        let mut info = LineInfo::new();
        info.push(usize::MAX);
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(usize::MAX - 1), 0);
        assert_eq!(info.line(usize::MAX), 1);
    }

    #[test]
    fn test_2_breaks_at_max_offset() {
        let mut info = LineInfo::new();
        for _ in 0..32 {
            info.push(usize::MAX);
        }
        assert_eq!(info.line(0), 0);
        assert_eq!(info.line(1), 0);
        assert_eq!(info.line(usize::MAX - 1), 0);
        assert_eq!(info.line(usize::MAX), 32);
    }
}
