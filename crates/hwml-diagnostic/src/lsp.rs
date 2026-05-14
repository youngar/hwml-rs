use crate::types::{Diagnostic, DiagnosticSeverity, Loctext, Position, Span};
use lsp_types::{
    Diagnostic as LspDiagnostic, DiagnosticRelatedInformation, DiagnosticSeverity as LspSeverity,
    Location, NumberOrString, Range, Uri,
};
use url::Url;

pub fn position_to_lsp(pos: &Position) -> lsp_types::Position {
    lsp_types::Position::new(
        (pos.line_num.saturating_sub(1)) as u32,
        (pos.offset.saturating_sub(pos.start_of_line)) as u32,
    )
}

pub fn span_to_lsp_range(span: &Span) -> Range {
    Range::new(position_to_lsp(&span.start), position_to_lsp(&span.end))
}

fn loctext_to_related_info(
    loctext: &Loctext,
    file_uri: &Uri,
) -> Option<DiagnosticRelatedInformation> {
    loctext.loc.as_ref().map(|span| {
        let range = span_to_lsp_range(span);
        let location = Location::new(file_uri.clone(), range);
        DiagnosticRelatedInformation {
            location,
            message: loctext.text.clone(),
        }
    })
}

fn severity_to_lsp(severity: DiagnosticSeverity) -> LspSeverity {
    match severity {
        DiagnosticSeverity::Bug => LspSeverity::ERROR,
        DiagnosticSeverity::Error => LspSeverity::ERROR,
        DiagnosticSeverity::Warning => LspSeverity::WARNING,
        DiagnosticSeverity::Info => LspSeverity::INFORMATION,
        DiagnosticSeverity::Hint => LspSeverity::HINT,
    }
}

pub fn diagnostic_to_lsp(diag: &Diagnostic, file_uri: &Uri, source: Option<&str>) -> LspDiagnostic {
    let range = span_to_lsp_range(&diag.span);
    let severity = Some(severity_to_lsp(diag.severity));
    let code = diag
        .code
        .as_ref()
        .map(|c| NumberOrString::String(c.0.clone()));
    let message = diag.message.clone();

    let mut related_information = Vec::new();
    for remark in &diag.extra_remarks {
        if let Some(info) = loctext_to_related_info(remark, file_uri) {
            related_information.push(info);
        }
    }

    LspDiagnostic {
        range,
        severity,
        code,
        code_description: None,
        source: source.map(|s| s.to_string()),
        message,
        related_information: if related_information.is_empty() {
            None
        } else {
            Some(related_information)
        },
        tags: None,
        data: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{DiagnosticCode, Loctext};
    use std::str::FromStr;

    #[test]
    fn test_position_to_lsp() {
        let pos = Position::new(42, 0, 5);
        let lsp_pos = position_to_lsp(&pos);
        assert_eq!(lsp_pos.line, 4);
        assert_eq!(lsp_pos.character, 42);
    }

    #[test]
    fn test_position_to_lsp_with_offset() {
        let pos = Position::new(50, 40, 3);
        let lsp_pos = position_to_lsp(&pos);
        assert_eq!(lsp_pos.line, 2);
        assert_eq!(lsp_pos.character, 10);
    }

    #[test]
    fn test_span_to_lsp_range() {
        let span = Span::new(Position::new(0, 0, 1), Position::new(5, 0, 1));
        let range = span_to_lsp_range(&span);
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 0);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 5);
    }

    #[test]
    fn test_severity_to_lsp() {
        assert_eq!(severity_to_lsp(DiagnosticSeverity::Bug), LspSeverity::ERROR);
        assert_eq!(
            severity_to_lsp(DiagnosticSeverity::Error),
            LspSeverity::ERROR
        );
        assert_eq!(
            severity_to_lsp(DiagnosticSeverity::Warning),
            LspSeverity::WARNING
        );
        assert_eq!(
            severity_to_lsp(DiagnosticSeverity::Info),
            LspSeverity::INFORMATION
        );
        assert_eq!(severity_to_lsp(DiagnosticSeverity::Hint), LspSeverity::HINT);
    }

    #[test]
    fn test_diagnostic_to_lsp_basic() {
        let diag = Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: Span::new(Position::new(10, 0, 2), Position::new(15, 0, 2)),
            message: "type mismatch".to_string(),
            code: Some(DiagnosticCode("E0001".to_string())),
            explanation: None,
            suggestions: vec![],
            related: vec![],
            backtrace: vec![],
            extra_remarks: vec![],
        };

        let uri = Uri::from_str("file:///test.hwml").unwrap();
        let lsp_diag = diagnostic_to_lsp(&diag, &uri, Some("hwml"));

        assert_eq!(lsp_diag.severity, Some(LspSeverity::ERROR));
        assert_eq!(lsp_diag.message, "type mismatch");
        assert_eq!(
            lsp_diag.code,
            Some(NumberOrString::String("E0001".to_string()))
        );
        assert_eq!(lsp_diag.source, Some("hwml".to_string()));
        assert_eq!(lsp_diag.related_information, None);
    }

    #[test]
    fn test_diagnostic_to_lsp_with_related() {
        let diag = Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: Span::new(Position::new(10, 0, 2), Position::new(15, 0, 2)),
            message: "type mismatch".to_string(),
            code: None,
            explanation: None,
            suggestions: vec![],
            related: vec![],
            backtrace: vec![],
            extra_remarks: vec![Loctext {
                loc: Some(Span::new(Position::new(5, 0, 1), Position::new(6, 0, 1))),
                text: "variable defined here".to_string(),
            }],
        };

        let uri = Uri::from_str("file:///test.hwml").unwrap();
        let lsp_diag = diagnostic_to_lsp(&diag, &uri, None);

        assert!(lsp_diag.related_information.is_some());
        let related = lsp_diag.related_information.unwrap();
        assert_eq!(related.len(), 1);
        assert_eq!(related[0].message, "variable defined here");
    }
}
