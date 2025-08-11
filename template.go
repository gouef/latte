package latte

// --- file: template.go -------------------------------------------------------
// Minimal Latte-like engine with custom parser, n:-attributes, and expr-based
// evaluation + pipe filters (User.Role|upper|default("N/A")).
// Configurable delimiters (default Go-like double braces {{ ... }}).

import (
	"bytes"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strings"

	htmlstd "html"

	exprlib "github.com/expr-lang/expr"
	"github.com/expr-lang/expr/vm"
	htmlpkg "golang.org/x/net/html"
)

// Loader abstracts how files are read (for layouts/includes).
// Provide OSLoader in production and a fake in tests.
type Loader interface {
	ReadFile(name string) (string, error)
}

type OSLoader struct{ BaseDir string }

func (l OSLoader) ReadFile(name string) (string, error) {
	p := name
	if l.BaseDir != "" && !filepath.IsAbs(name) {
		p = filepath.Join(l.BaseDir, name)
	}
	b, err := os.ReadFile(p)
	if err != nil {
		return "", err
	}
	return string(b), nil
}

// --- Delimiters & Regex compilation -----------------------------------------

type Delims struct{ L, R string }

var DefaultDelims = Delims{L: "{{", R: "}}"}

type regexSet struct {
	extendsRe, blockRe, snippetRe, includeRe *regexp.Regexp
	blockPlaceholderRe                       *regexp.Regexp
	outEscRe, outRawRe                       *regexp.Regexp
}

func compileRegex(d Delims) regexSet {
	LM := regexp.QuoteMeta(d.L)
	RM := regexp.QuoteMeta(d.R)
	return regexSet{
		extendsRe:          regexp.MustCompile(`(?m)^\s*` + LM + `\s*extends\s+"([^"]+)"\s*` + RM),
		blockRe:            regexp.MustCompile(`(?s)` + LM + `\s*block\s+"([^"]+)"\s*` + RM + `(.*?)` + LM + `\s*/block\s*` + RM),
		snippetRe:          regexp.MustCompile(`(?s)` + LM + `\s*snippet\s+"([^"]+)"\s*` + RM + `(.*?)` + LM + `\s*/snippet\s*` + RM),
		includeRe:          regexp.MustCompile(`(?s)` + LM + `\s*include\s+"([^"]+)"\s*` + RM),
		blockPlaceholderRe: regexp.MustCompile(LM + `\s*block:([a-zA-Z0-9_:\-]+)\s*` + RM),
		outEscRe:           regexp.MustCompile(`(?s)` + LM + `=\s*(.*?)\s*` + RM),
		outRawRe:           regexp.MustCompile(`(?s)` + LM + `!\s*(.*?)\s*!` + RM),
	}
}

// --- Evaluator ---------------------------------------------------------------

type Evaluator interface {
	EvalBool(expr string, data any) (bool, error)
	EvalValue(expr string, data any) (any, error)
}

// ExprEval uses github.com/cantonment/expr to evaluate expressions against data.
// Supports pipe filters like `User.Role|upper|default("N/A")` by transforming
// them into nested function calls: default(upper(User.Role), "N/A").
type ExprEval struct{ Functions map[string]any }

func (e ExprEval) getProgram(expression string, data any) (*vm.Program, error) {
	expression = transformPipes(expression)
	opts := []exprlib.Option{exprlib.Env(data)}
	functions := defaultExprFuncs()
	for k, v := range GlobalExprFunctions {
		functions[k] = v
	}
	for k, v := range e.Functions {
		functions[k] = v
	}
	for name, fn := range functions {
		//opts = append(opts, exprlib.Function(name, fn))
		opts = append(opts, exprlib.Function(name, wrapExprFunc(fn)))
	}
	return exprlib.Compile(expression, opts...)
}

func (e ExprEval) EvalBool(expression string, data any) (bool, error) {
	program, err := e.getProgram(expression, data)
	if err != nil {
		return false, err
	}
	v, err := exprlib.Run(program, data)
	if err != nil {
		return false, err
	}
	return toBool(v), nil
}

func (e ExprEval) EvalValue(expression string, data any) (any, error) {
	program, err := e.getProgram(expression, data)
	if err != nil {
		return nil, err
	}
	return exprlib.Run(program, data)
}

// DumbEval Dumb fallback evaluator (literals only)
type DumbEval struct{}

func (DumbEval) EvalBool(expr string, _ any) (bool, error) {
	s := strings.TrimSpace(strings.ToLower(strings.TrimSpace(expr)))
	if s == "true" || s == "1" {
		return true, nil
	}
	if s == "false" || s == "0" || s == "" {
		return false, nil
	}
	return true, nil
}
func (DumbEval) EvalValue(expr string, _ any) (any, error) { return strings.TrimSpace(expr), nil }

// toBool coerces arbitrary values to bool
func toBool(v any) bool {
	switch x := v.(type) {
	case bool:
		return x
	case int, int64, int32, int16, int8:
		return reflect.ValueOf(x).Int() != 0
	case uint, uint64, uint32, uint16, uint8:
		return reflect.ValueOf(x).Uint() != 0
	case float64, float32:
		return reflect.ValueOf(x).Float() != 0
	case string:
		s := strings.TrimSpace(strings.ToLower(x))
		return s != "" && s != "0" && s != "false"
	default:
		return x != nil
	}
}

// --- n:-attribute extension API ---------------------------------------------

type NAttrHandler func(*NContext) error

type NContext struct {
	Node             *htmlpkg.Node
	Value            string
	T                *Template
	Data             any
	Eval             Evaluator
	Remove           func()
	AppendClass      func(string)
	SetAttr          func(string, string)
	GetAttr          func(string) string
	CaptureInnerHTML func() string
}

var GlobalNAttrHandlers = map[string]NAttrHandler{}

func RegisterNAttr(name string, h NAttrHandler) { GlobalNAttrHandlers[name] = h }

// --- Template/runtime --------------------------------------------------------

type Template struct {
	Name           string
	Source         string
	Layout         string
	Blocks         map[string]string
	Snippets       map[string]string
	SnippetClasses map[string]string
	Delims         Delims
	rx             regexSet
}

func NewTemplate(name string) *Template {
	return &Template{
		Name:           name,
		Blocks:         make(map[string]string),
		Snippets:       make(map[string]string),
		SnippetClasses: make(map[string]string),
		Delims:         DefaultDelims,
		rx:             compileRegex(DefaultDelims),
	}
}

// Execute renders the template (layout + blocks) and then processes n:* attrs.
func (t *Template) Execute(loader Loader, eval Evaluator, data any) (string, error) {
	return t.ExecuteWith(loader, eval, data, nil)
}

// ExecuteWith allows injecting custom n:-attribute handlers from outside.
// Order of precedence: defaults < global < provided
func (t *Template) ExecuteWith(loader Loader, eval Evaluator, data any, handlers map[string]NAttrHandler) (string, error) {
	if eval == nil {
		eval = DumbEval{}
	}

	var out string
	if t.Layout != "" {
		layoutSrc, err := loader.ReadFile(t.Layout)
		if err != nil {
			return "", fmt.Errorf("unable to load layout %q: %w", t.Layout, err)
		}
		out = layoutSrc
		for name, content := range t.Blocks {
			out = replaceBlockPlaceholder(out, t.Delims, name, content)
		}
		out = t.rx.blockPlaceholderRe.ReplaceAllString(out, "")
	} else {
		out = t.Source
		for name, content := range t.Blocks {
			out = replaceBlockPlaceholder(out, t.Delims, name, content)
		}
		out = t.rx.blockPlaceholderRe.ReplaceAllString(out, "")
	}

	merged := map[string]NAttrHandler{}
	for k, v := range GlobalNAttrHandlers {
		merged[k] = v
	}
	for k, v := range handlers {
		merged[k] = v
	}

	processed, err := processNAttrs(out, eval, t, data, merged)
	if err != nil {
		return "", err
	}
	final, err := processOutputs(processed, eval, data, t.rx.outEscRe, t.rx.outRawRe)
	if err != nil {
		return "", err
	}
	return final, nil
}

func (t *Template) placeholder(name string) string {
	return t.Delims.L + " block:" + name + " " + t.Delims.R
}

func replaceBlockPlaceholder(src string, d Delims, name, content string) string {
	LM := regexp.QuoteMeta(d.L)
	RM := regexp.QuoteMeta(d.R)
	re := regexp.MustCompile(`(?s)` + LM + `\s*block:` + regexp.QuoteMeta(name) + `\s*` + RM)
	return re.ReplaceAllString(src, content)
}

// --- Parser ------------------------------------------------------------------

type Parser struct {
	Loader Loader
	delims Delims
	rx     regexSet
}

func NewParser(loader Loader) *Parser { return NewParserWithDelims(loader, DefaultDelims) }

func NewParserWithDelims(loader Loader, d Delims) *Parser {
	return &Parser{Loader: loader, delims: d, rx: compileRegex(d)}
}

// Delims sets the parser delimiters (same semantics as html/template.Delims).
// Call this BEFORE Parse/ParseFile/ParseGlob. Chainable.
func (p *Parser) Delims(left, right string) *Parser {
	p.delims = Delims{L: left, R: right}
	p.rx = compileRegex(p.delims)
	return p
}

func (p *Parser) Parse(name, src string) (*Template, error) { return p.parse(name, src) }

func (p *Parser) ParseFile(path string) (*Template, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return p.parse(filepath.Base(path), string(b))
}

func (p *Parser) ParseGlob(pattern string) ([]*Template, error) {
	matches, err := filepath.Glob(pattern)
	if err != nil {
		return nil, err
	}
	var out []*Template
	for _, path := range matches {
		t, err := p.ParseFile(path)
		if err != nil {
			return nil, err
		}
		out = append(out, t)
	}
	return out, nil
}

func (p *Parser) ParseFS(fsys fs.FS, patterns ...string) ([]*Template, error) {
	var out []*Template
	for _, pattern := range patterns {
		err := fs.WalkDir(fsys, ".", func(path string, d fs.DirEntry, err error) error {
			if err != nil || d.IsDir() || !match(pattern, path) {
				return nil
			}
			b, rerr := fs.ReadFile(fsys, path)
			if rerr != nil {
				return rerr
			}
			t, rerr := p.parse(filepath.Base(path), string(b))
			if rerr != nil {
				return rerr
			}
			out = append(out, t)
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	return out, nil
}

// Internal parse with include expansion and directive extraction.
func (p *Parser) parse(name, src string) (*Template, error) {
	t := NewTemplate(name)
	t.Delims = p.delims
	t.rx = p.rx

	expanded, err := p.expandIncludes(src)
	if err != nil {
		return nil, err
	}
	t.Source = expanded

	if m := p.rx.extendsRe.FindStringSubmatch(expanded); m != nil {
		t.Layout = m[1]
		t.Source = p.rx.extendsRe.ReplaceAllString(t.Source, "")
	}

	for _, m := range p.rx.blockRe.FindAllStringSubmatch(t.Source, -1) {
		bname := m[1]
		body := strings.TrimSpace(m[2])
		t.Blocks[bname] = body
	}
	t.Source = p.rx.blockRe.ReplaceAllStringFunc(t.Source, func(m string) string {
		mm := p.rx.blockRe.FindStringSubmatch(m)
		return t.placeholder(mm[1])
	})

	for _, m := range p.rx.snippetRe.FindAllStringSubmatch(t.Source, -1) {
		sname := m[1]
		body := strings.TrimSpace(m[2])
		t.Snippets[sname] = body
	}
	t.Source = p.rx.snippetRe.ReplaceAllString(t.Source, "")

	return t, nil
}

// expand include directive
func (p *Parser) expandIncludes(src string) (string, error) {
	return p.rx.includeRe.ReplaceAllStringFunc(src, func(m string) string {
		sub := p.rx.includeRe.FindStringSubmatch(m)
		if len(sub) < 2 {
			return m
		}
		fname := sub[1]
		if p.Loader == nil {
			return ""
		}
		content, err := p.Loader.ReadFile(fname)
		if err != nil {
			return ""
		}
		if expanded, e2 := p.expandIncludes(content); e2 == nil {
			return expanded
		}
		return content
	}), nil
}

// --- n:-attributes processing ------------------------------------------------

// Supported now:
//  - n:if="expr"            : drops node if false
//  - n:class="expr"         : appends evaluated string to class
//  - n:snippet="name"       : captures inner HTML into Template.Snippets[name]
//                              and appends classes: "snippet" and "snippet--NAME"
// NOTE: n:* attributes are processing-only and removed from output.

func processNAttrs(src string, eval Evaluator, t *Template, data any, handlers map[string]NAttrHandler) (string, error) {
	nodes, err := htmlpkg.ParseFragment(strings.NewReader(src), &htmlpkg.Node{Type: htmlpkg.ElementNode, Data: "div"})
	if err != nil {
		return "", err
	}
	root := &htmlpkg.Node{Type: htmlpkg.ElementNode, Data: "div"}
	for _, n := range nodes {
		root.AppendChild(n)
	}

	var walk func(n *htmlpkg.Node)
	walk = func(n *htmlpkg.Node) {
		if n.Type == htmlpkg.ElementNode {
			// collect n:* attributes and strip them from output
			var todo [][2]string
			outAttrs := make([]htmlpkg.Attribute, 0, len(n.Attr))
			for _, a := range n.Attr {
				if strings.HasPrefix(a.Key, "n:") {
					todo = append(todo, [2]string{a.Key, a.Val})
					continue
				}
				outAttrs = append(outAttrs, a)
			}
			n.Attr = outAttrs

			ctx := &NContext{
				Node:        n,
				T:           t,
				Data:        data,
				Eval:        eval,
				Remove:      func() { removeNode(n) },
				AppendClass: func(s string) { appendClass(n, s) },
				SetAttr:     func(k, v string) { setAttr(n, k, v) },
				GetAttr:     func(k string) string { return getAttr(n, k) },
				CaptureInnerHTML: func() string {
					var bb bytes.Buffer
					for ch := n.FirstChild; ch != nil; ch = ch.NextSibling {
						_ = htmlpkg.Render(&bb, ch)
					}
					return bb.String()
				},
			}

			for _, kv := range todo {
				name, val := kv[0], kv[1]
				ctx.Value = val
				if h, ok := handlers[name]; ok {
					_ = h(ctx)
					if n.Parent == nil {
						return
					} // removed
				}
			}

			for c := n.FirstChild; c != nil; {
				next := c.NextSibling
				walk(c)
				c = next
			}
			return
		}
		for c := n.FirstChild; c != nil; {
			next := c.NextSibling
			walk(c)
			c = next
		}
	}

	for c := root.FirstChild; c != nil; {
		next := c.NextSibling
		walk(c)
		c = next
	}

	var out bytes.Buffer
	for ch := root.FirstChild; ch != nil; ch = ch.NextSibling {
		_ = htmlpkg.Render(&out, ch)
	}
	return out.String(), nil
}

func removeNode(n *htmlpkg.Node) {
	if n.Parent == nil {
		return
	}
	p := n.Parent
	if p.FirstChild == n {
		p.FirstChild = n.NextSibling
	}
	if p.LastChild == n {
		p.LastChild = n.PrevSibling
	}
	if n.PrevSibling != nil {
		n.PrevSibling.NextSibling = n.NextSibling
	}
	if n.NextSibling != nil {
		n.NextSibling.PrevSibling = n.PrevSibling
	}
	n.Parent, n.PrevSibling, n.NextSibling = nil, nil, nil
}

func setAttr(n *htmlpkg.Node, key, val string) {
	for i := range n.Attr {
		if n.Attr[i].Key == key {
			n.Attr[i].Val = val
			return
		}
	}
	n.Attr = append(n.Attr, htmlpkg.Attribute{Key: key, Val: val})
}

func getAttr(n *htmlpkg.Node, key string) string {
	for _, a := range n.Attr {
		if a.Key == key {
			return a.Val
		}
	}
	return ""
}

func appendClass(n *htmlpkg.Node, add string) {
	cls := getAttr(n, "class")
	if cls == "" {
		setAttr(n, "class", add)
		return
	}
	setAttr(n, "class", strings.TrimSpace(cls+" "+add))
}

// --- regex helpers & output expressions -------------------------------------

func match(pattern, name string) bool { matched, _ := filepath.Match(pattern, name); return matched }

// output expressions: {{= expr }} (escaped), {{! expr !}} (raw)
func processOutputs(src string, eval Evaluator, data any, outEscRe, outRawRe *regexp.Regexp) (string, error) {
	// raw first to avoid double-escaping
	out := outRawRe.ReplaceAllStringFunc(src, func(m string) string {
		sub := outRawRe.FindStringSubmatch(m)
		if len(sub) < 2 {
			return ""
		}
		expr := transformPipes(sub[1])
		v, err := eval.EvalValue(expr, data)
		if err != nil {
			return ""
		}
		return fmt.Sprint(v)
	})
	out = outEscRe.ReplaceAllStringFunc(out, func(m string) string {
		sub := outEscRe.FindStringSubmatch(m)
		if len(sub) < 2 {
			return ""
		}
		expr := transformPipes(sub[1])
		v, err := eval.EvalValue(expr, data)
		if err != nil {
			return ""
		}
		return htmlstd.EscapeString(fmt.Sprint(v))
	})
	return out, nil
}

// transformPipes converts Latte-like pipes into nested function calls.
//
//	User.Role|upper|default("N/A")  =>  default(upper(User.Role), "N/A")
//
// Also supports arg form:  price|fmt:2 => fmt(price, 2)
func transformPipes(expr string) string {
	tokens := splitPipes(expr)
	if len(tokens) == 1 {
		return strings.TrimSpace(expr)
	}
	base := strings.TrimSpace(tokens[0])
	cur := base
	for _, f := range tokens[1:] {
		f = strings.TrimSpace(f)
		if f == "" {
			continue
		}
		name, args := parseFilterToken(f)
		if args == "" {
			cur = fmt.Sprintf("%s(%s)", name, cur)
		} else {
			cur = fmt.Sprintf("%s(%s, %s)", name, cur, args)
		}
	}
	return cur
}

func splitPipes(s string) []string {
	var out []string
	var sb strings.Builder
	depth := 0
	inS, inD := false, false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c == '\'' && !inD {
			inS = !inS
			sb.WriteByte(c)
			continue
		}
		if c == '"' && !inS {
			inD = !inD
			sb.WriteByte(c)
			continue
		}
		if inS || inD {
			sb.WriteByte(c)
			continue
		}
		switch c {
		case '(':
			depth++
			sb.WriteByte(c)
		case ')':
			if depth > 0 {
				depth--
			}
			sb.WriteByte(c)
		case '|':
			if depth == 0 {
				out = append(out, strings.TrimSpace(sb.String()))
				sb.Reset()
				continue
			}
			sb.WriteByte(c)
		default:
			sb.WriteByte(c)
		}
	}
	out = append(out, strings.TrimSpace(sb.String()))
	return out
}

// parse filter token in forms: "upper" | "fmt(2)" | "fmt:2, 'x'"
func parseFilterToken(tok string) (name string, args string) {
	if i := strings.IndexByte(tok, '('); i != -1 && strings.HasSuffix(tok, ")") {
		return strings.TrimSpace(tok[:i]), strings.TrimSpace(tok[i+1 : len(tok)-1])
	}
	if i := strings.IndexByte(tok, ':'); i != -1 {
		return strings.TrimSpace(tok[:i]), strings.TrimSpace(tok[i+1:])
	}
	return strings.TrimSpace(tok), ""
}

// Helper: wrap any function into expr-compatible func(...any)(any,error)
func wrapExprFunc(fn any) func(params ...any) (any, error) {
	if f, ok := fn.(func(params ...any) (any, error)); ok {
		return f
	}
	v := reflect.ValueOf(fn)
	if v.Kind() != reflect.Func {
		return func(params ...any) (any, error) { return fn, nil }
	}
	t := v.Type()
	coerce := func(pv any, pt reflect.Type) reflect.Value {
		if pt.Kind() == reflect.Interface && pt.NumMethod() == 0 { // interface{}
			return reflect.ValueOf(pv)
		}
		if pv == nil {
			return reflect.Zero(pt)
		}
		rv := reflect.ValueOf(pv)
		if rv.IsValid() && rv.Type().AssignableTo(pt) {
			return rv
		}
		if rv.IsValid() && rv.Type().ConvertibleTo(pt) {
			return rv.Convert(pt)
		}
		if pt.Kind() == reflect.String {
			return reflect.ValueOf(fmt.Sprint(pv))
		}
		return reflect.Zero(pt)
	}
	return func(params ...any) (any, error) {
		var args []reflect.Value
		nIn := t.NumIn()
		if t.IsVariadic() {
			fixed := nIn - 1
			for i := 0; i < fixed; i++ {
				args = append(args, coerce(getAt(params, i), t.In(i)))
			}
			elem := t.In(nIn - 1).Elem()
			for i := fixed; i < len(params); i++ {
				args = append(args, coerce(params[i], elem))
			}
		} else {
			for i := 0; i < nIn; i++ {
				args = append(args, coerce(getAt(params, i), t.In(i)))
			}
		}
		res := v.Call(args)
		if ln := len(res); ln > 0 {
			// if last is error, handle it
			last := res[ln-1]
			errT := reflect.TypeOf((*error)(nil)).Elem()
			if last.IsValid() && last.Type().Implements(errT) {
				if !last.IsNil() {
					return nil, last.Interface().(error)
				}
				if ln >= 2 {
					return res[0].Interface(), nil
				}
				return nil, nil
			}
			return res[0].Interface(), nil
		}
		return nil, nil
	}
}

func getAt(params []any, i int) any {
	if i < len(params) {
		return params[i]
	}
	return nil
}

// --- file: expr_funcs.go -----------------------------------------------------

// GlobalExprFunctions Global registry for expr functions
var GlobalExprFunctions = map[string]any{}

func RegisterExprFunc(name string, fn any) { GlobalExprFunctions[name] = fn }

func defaultExprFuncs() map[string]any {
	return map[string]any{
		"len":      lenAny,
		"upper":    strings.ToUpper,
		"lower":    strings.ToLower,
		"trim":     strings.TrimSpace,
		"slug":     slugify,
		"join":     joinAny,
		"contains": containsAny,
		"default":  defaultIf,
		"coalesce": coalesce,
		"tern": func(cond bool, a, b any) any {
			if cond {
				return a
			}
			return b
		},
	}
}

func lenAny(v any) int {
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.String, reflect.Array, reflect.Slice, reflect.Map:
		return rv.Len()
	default:
		return 0
	}
}

var reNonAlnum = regexp.MustCompile(`[^\p{L}\p{N}]+`)
var reDash = regexp.MustCompile(`-+`)

func slugify(s string) string {
	s = strings.ToLower(strings.TrimSpace(s))
	s = reNonAlnum.ReplaceAllString(s, "-")
	s = reDash.ReplaceAllString(s, "-")
	s = strings.Trim(s, "-")
	return s
}

func joinAny(arr any, sep string) string {
	rv := reflect.ValueOf(arr)
	if rv.Kind() != reflect.Slice && rv.Kind() != reflect.Array {
		return ""
	}
	parts := make([]string, rv.Len())
	for i := 0; i < rv.Len(); i++ {
		parts[i] = fmt.Sprint(rv.Index(i).Interface())
	}
	return strings.Join(parts, sep)
}

func containsAny(hay any, needle any) bool {
	switch h := hay.(type) {
	case string:
		return strings.Contains(h, fmt.Sprint(needle))
	}
	rv := reflect.ValueOf(hay)
	switch rv.Kind() {
	case reflect.Slice, reflect.Array:
		for i := 0; i < rv.Len(); i++ {
			if fmt.Sprint(rv.Index(i).Interface()) == fmt.Sprint(needle) {
				return true
			}
		}
		return false
	case reflect.Map:
		key := reflect.ValueOf(needle)
		if key.IsValid() {
			return rv.MapIndex(key).IsValid()
		}
		return false
	default:
		return false
	}
}

func isZero(v any) bool {
	if v == nil {
		return true
	}
	rv := reflect.ValueOf(v)
	switch rv.Kind() {
	case reflect.Bool:
		return !rv.Bool()
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return rv.Int() == 0
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return rv.Uint() == 0
	case reflect.Float32, reflect.Float64:
		return rv.Float() == 0
	case reflect.String:
		return rv.Len() == 0
	case reflect.Slice, reflect.Array, reflect.Map:
		return rv.Len() == 0
	case reflect.Interface, reflect.Pointer:
		return rv.IsNil()
	default:
		z := reflect.Zero(rv.Type()).Interface()
		return reflect.DeepEqual(v, z)
	}
}

func defaultIf(v any, def any) any {
	if isZero(v) {
		return def
	}
	return v
}

func coalesce(vals ...any) any {
	for _, v := range vals {
		if !isZero(v) {
			return v
		}
	}
	return nil
}
