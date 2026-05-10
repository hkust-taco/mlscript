import { EditorView, basicSetup } from 'https://esm.sh/codemirror@6.0.1';
import { javascript } from 'https://esm.sh/@codemirror/lang-javascript@6.2.4';
import { StreamLanguage } from 'https://esm.sh/@codemirror/language@6.11.3';
import { vscodeLight as theme } from "https://esm.sh/@uiw/codemirror-theme-vscode";
import Highlight from "./Highlight.mjs";
import fs from "../filesystem/fs.mjs";

export function createEditor(container, initialContent, filePath, extension, readonly = false) {
  // Determine language based on file extension
  let languageExtension = [theme];
  if (extension === "mjs" || extension === "js") {
    languageExtension.push(javascript());
  } else if (extension === "mls") {
    languageExtension.push(
      StreamLanguage.define({
        ...Highlight.mlscript,
        token: (stream, state) => Highlight.mlscript.token(stream, state),
      })
    );
  }

  // Create CodeMirror editor
  const editorView = new EditorView({
    doc: initialContent,
    extensions: [
      basicSetup,
      ...languageExtension,
      EditorView.updateListener.of((update) => {
        if (readonly) return;
        if (update.docChanged) {
          // Auto-save on content change
          const newContent = update.state.doc.toString();
          fs.write(filePath, newContent);
        }
      }),
      readonly ? EditorView.editable.of(false) : [],
      EditorView.theme({
        "&": {
          height: "100%",
          fontSize: "14px",
        },
        ".cm-scroller": {
          overflow: "auto",
        },
        ".cm-content": {
          caretColor: "var(--sand-12)",
          fontFamily:
            "'Google Sans Code', 'Monaco', 'Menlo', 'Ubuntu Mono', monospace",
        },
        ".cm-lineNumbers": {
          fontFamily:
            "'Google Sans Code', 'Monaco', 'Menlo', 'Ubuntu Mono', monospace",
        },
        ".cm-cursor": {
          borderLeftColor: "var(--sand-12)",
        },
        ".cm-editor .cm-gutters": {
          backgroundColor: "var(--sand-2)",
          color: "var(--sand-11)",
          borderRight: "1px solid var(--sand-6)",
        },
        ".cm-activeLineGutter": {
          backgroundColor: "var(--sand-2)",
        },
      }),
    ],
    parent: container,
  });
  
  return editorView;
}
