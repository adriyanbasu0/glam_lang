use crate::ast::{BlockStatement, Expression, Program, Statement};
use crate::token::TokenKind;
use rand::Rng;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub const NULL: Object = Object::Null;
pub const TRUE: Object = Object::Boolean(true);
pub const FALSE: Object = Object::Boolean(false);

#[derive(Debug, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    String(String),
    Return(Box<Object>),
    Function(Function),
    Builtin(fn(Vec<Object>) -> Object),
    Some(Box<Object>),
    Ok,
    Null,
    Error(String),
}

pub struct Function {
    pub parameters: Vec<crate::ast::Identifier>,
    pub body: BlockStatement,
    pub env: Rc<RefCell<Environment>>,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Function")
            .field("parameters", &self.parameters)
            .field("body", &self.body)
            .field("env", &"// Rc<RefCell<Environment>>") // Placeholder for env
            .finish()
    }
}

impl Clone for Function {
    fn clone(&self) -> Self {
        Function {
            parameters: self.parameters.clone(),
            body: self.body.clone(),
            env: self.env.clone(),
        }
    }
}

impl Object {
    pub fn is_truthy(&self) -> bool {
        match self {
            Object::Null => false,
            Object::Boolean(b) => *b,
            _ => true,
        }
    }

    pub fn type_str(&self) -> &str {
        match self {
            Object::Integer(_) => "INTEGER",
            Object::Boolean(_) => "BOOLEAN",
            Object::String(_) => "STRING",
            Object::Return(_) => "RETURN_VALUE",
            Object::Function(_) => "FUNCTION",
            Object::Builtin(_) => "BUILTIN",
            Object::Some(_) => "SOME",
            Object::Ok => "OK",
            Object::Null => "NULL",
            Object::Error(_) => "ERROR",
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Object::Integer(value) => write!(f, "{}", value),
            Object::Boolean(value) => write!(f, "{}", value),
            Object::String(value) => write!(f, "{}", value),
            Object::Return(value) => write!(f, "{}", value),
            Object::Function(func) => {
                let params: Vec<String> = func.parameters.iter().map(|p| p.value.clone()).collect();
                write!(f, "fn({}) {{ ... }}", params.join(", "))
            }
            Object::Builtin(_) => write!(f, "builtin function"),
            Object::Some(value) => write!(f, "some({})", value),
            Object::Ok => write!(f, "ok"),
            Object::Null => write!(f, "null"),
            Object::Error(value) => write!(f, "ERROR: {}", value),
        }
    }
}

pub struct Environment {
    store: HashMap<String, Object>,
    outer: Option<Rc<RefCell<Environment>>>,
    pub writer: Rc<RefCell<dyn std::io::Write>>,
}

pub fn builtin_type(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "Wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }
    Object::String(args[0].type_str().to_string())
}

pub fn builtin_rand(args: Vec<Object>) -> Object {
    if args.len() != 2 {
        return Object::Error(format!(
            "Wrong number of arguments. got={}, want=2",
            args.len()
        ));
    }

    let min = match args[0] {
        Object::Integer(i) => i,
        _ => {
            return Object::Error(format!(
                "Argument must be an integer, got {}",
                args[0].type_str()
            ));
        }
    };

    let max = match args[1] {
        Object::Integer(i) => i,
        _ => {
            return Object::Error(format!(
                "Argument must be an integer, got {}",
                args[1].type_str()
            ));
        }
    };

    let mut rng = rand::thread_rng();
    Object::Integer(rng.gen_range(min..=max))
}

pub fn builtin_some(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "Wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }
    Object::Some(Box::new(args[0].clone()))
}

pub fn builtin_err(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "Wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }
    match &args[0] {
        Object::String(s) => Object::Error(s.clone()),
        _ => Object::Error(format!(
            "Argument to `err` must be a string, got {}",
            args[0].type_str()
        )),
    }
}

pub fn builtin_ok(args: Vec<Object>) -> Object {
    if !args.is_empty() {
        return Object::Error(format!(
            "Wrong number of arguments. got={}, want=0",
            args.len()
        ));
    }
    Object::Ok
}

impl Environment {
    pub fn new(writer: Rc<RefCell<dyn std::io::Write>>) -> Self {
        let mut store = HashMap::new();
        store.insert("ok".to_string(), Object::Builtin(builtin_ok));
        store.insert("some".to_string(), Object::Builtin(builtin_some));
        store.insert("err".to_string(), Object::Builtin(builtin_err));
        store.insert("type".to_string(), Object::Builtin(builtin_type));
        store.insert("rand".to_string(), Object::Builtin(builtin_rand));
        Environment {
            store,
            outer: None,
            writer,
        }
    }

    pub fn new_enclosed_environment(outer: Rc<RefCell<Environment>>) -> Self {
        let writer = outer.borrow().writer.clone();
        Environment {
            store: HashMap::new(),
            outer: Some(outer),
            writer,
        }
    }

    pub fn get(&self, name: &str) -> Option<Object> {
        match self.store.get(name) {
            Some(obj) => Some(obj.clone()),
            None => self.outer.as_ref().and_then(|e| e.borrow().get(name)),
        }
    }

    pub fn set(&mut self, name: String, val: Object) -> Object {
        self.store.insert(name, val.clone());
        val
    }
}

pub fn eval(program: Program, env: &mut Rc<RefCell<Environment>>) -> Object {
    let mut result = NULL;
    for statement in program.statements {
        result = eval_statement(statement, env.clone());
        if let Object::Return(value) = result {
            return *value;
        }
        if let Object::Error(_) = result {
            return result;
        }
    }
    result
}

fn eval_statement(statement: Statement, env: Rc<RefCell<Environment>>) -> Object {
    match statement {
        Statement::Expression(expr) => eval_expression(expr.expression, env),
        Statement::Return(ret_stmt) => {
            let val = eval_expression(ret_stmt.return_value, env);
            if is_error(&val) {
                return val;
            }
            Object::Return(Box::new(val))
        }
        Statement::Let(let_stmt) => {
            let val = eval_expression(let_stmt.value, env.clone());
            if is_error(&val) {
                return val;
            }
            env.borrow_mut().set(let_stmt.name.value, val)
        }
        Statement::Print(print_stmt) => eval_print_statement(print_stmt.expression, env),
    }
}

fn eval_print_statement(expression: Expression, env: Rc<RefCell<Environment>>) -> Object {
    let value = eval_expression(expression, env.clone());
    if is_error(&value) {
        return value;
    }
    let env_ref = env.borrow_mut();
    let mut writer = env_ref.writer.borrow_mut();
    writeln!(writer, "{}", value).expect("Failed to write to output");
    writer.flush().expect("Failed to flush output");
    NULL
}

fn eval_expression(expression: Expression, env: Rc<RefCell<Environment>>) -> Object {
    match expression {
        Expression::IntLiteral(int) => Object::Integer(int.value),
        Expression::Boolean(boolean) => native_bool_to_boolean_object(boolean.value),
        Expression::StringLiteral(s) => Object::String(s.value),
        Expression::Null => NULL,
        Expression::Prefix(prefix) => {
            let right = eval_expression(*prefix.right, env);
            if is_error(&right) {
                return right;
            }
            eval_prefix_expression(prefix.operator, right)
        }
        Expression::Infix(infix) => {
            let left = eval_expression(*infix.left, env.clone());
            if is_error(&left) {
                return left;
            }
            let right = eval_expression(*infix.right, env);
            if is_error(&right) {
                return right;
            }
            eval_infix_expression(infix.operator, left, right)
        }
        Expression::If(if_exp) => {
            let condition = eval_expression(*if_exp.condition, env.clone());
            if is_error(&condition) {
                return condition;
            }
            if condition.is_truthy() {
                eval_block_statement(if_exp.consequence, env)
            } else if let Some(alt) = if_exp.alternative {
                eval_block_statement(alt, env)
            } else {
                NULL
            }
        }
        Expression::Identifier(ident) => eval_identifier(ident, env),
        Expression::Function(func) => Object::Function(Function {
            parameters: func.parameters,
            body: func.body,
            env: env, // Capture the current Rc<RefCell<Environment>> directly
        }),
        Expression::Call(call_exp) => {
            let function = eval_expression(*call_exp.function, env.clone());
            if is_error(&function) {
                return function;
            }

            let args = eval_expressions(call_exp.arguments, env);
            apply_function(function, args)
        }
    }
}

fn eval_block_statement(block: BlockStatement, env: Rc<RefCell<Environment>>) -> Object {
    let mut result = NULL;
    for statement in block.statements {
        result = eval_statement(statement, env.clone());
        if let Object::Return(_) | Object::Error(_) = result {
            return result;
        }
    }
    result
}

fn eval_prefix_expression(operator: crate::token::Token, right: Object) -> Object {
    match operator.kind {
        TokenKind::Bang => eval_bang_operator_expression(right),
        TokenKind::Minus => eval_minus_operator_expression(right),
        _ => Object::Error(format!("Unknown operator: {:?}{:?}", operator.kind, right)),
    }
}

fn eval_bang_operator_expression(right: Object) -> Object {
    match right {
        Object::Boolean(true) => Object::Boolean(false),
        Object::Boolean(false) => Object::Boolean(true),
        Object::Null => Object::Boolean(true),
        _ => Object::Boolean(false),
    }
}

fn eval_minus_operator_expression(right: Object) -> Object {
    if let Object::Integer(value) = right {
        Object::Integer(-value)
    } else {
        Object::Error(format!("Unknown operator: -{:?}", right))
    }
}

fn eval_infix_expression(operator: crate::token::Token, left: Object, right: Object) -> Object {
    match (left, right) {
        (Object::Integer(l_val), Object::Integer(r_val)) => {
            eval_integer_infix_expression(operator, l_val, r_val)
        }
        (Object::Boolean(l_val), Object::Boolean(r_val)) => {
            eval_boolean_infix_expression(operator, l_val, r_val)
        }
        (Object::String(l_val), Object::String(r_val)) => {
            if operator.kind == TokenKind::Plus {
                Object::String(format!("{}{}", l_val, r_val))
            } else {
                Object::Error(format!(
                    "Unknown operator: {:?} {:?} {:?}",
                    l_val, operator.kind, r_val
                ))
            }
        }
        (l, r) if l.type_str() != r.type_str() => Object::Error(format!(
            "Type mismatch: {:?} {:?} {:?}",
            l.type_str(),
            operator.kind,
            r.type_str()
        )),
        (l, r) => Object::Error(format!("Unknown operator: {:?} {:?} {:?}", l, operator.kind, r)),
    }
}

fn eval_integer_infix_expression(operator: crate::token::Token, left: i64, right: i64) -> Object {
    match operator.kind {
        TokenKind::Plus => Object::Integer(left + right),
        TokenKind::Minus => Object::Integer(left - right),
        TokenKind::Asterisk => Object::Integer(left * right),
        TokenKind::Slash => Object::Integer(left / right),
        TokenKind::Lt => native_bool_to_boolean_object(left < right),
        TokenKind::Gt => native_bool_to_boolean_object(left > right),
        TokenKind::Eq => native_bool_to_boolean_object(left == right),
        TokenKind::NotEq => native_bool_to_boolean_object(left != right),
        _ => Object::Error(format!(
            "Unknown operator: {:?} {:?} {:?}",
            left, operator.kind, right
        )),
    }
}

fn eval_boolean_infix_expression(operator: crate::token::Token, left: bool, right: bool) -> Object {
    match operator.kind {
        TokenKind::Eq => native_bool_to_boolean_object(left == right),
        TokenKind::NotEq => native_bool_to_boolean_object(left != right),
        _ => Object::Error(format!(
            "Unknown operator: {:?} {:?} {:?}",
            left, operator.kind, right
        )),
    }
}

fn eval_identifier(ident: crate::ast::Identifier, env: Rc<RefCell<Environment>>) -> Object {
    if let Some(val) = env.borrow().get(&ident.value) {
        return val;
    }
    Object::Error(format!("Identifier not found: {}", ident.value))
}

fn eval_expressions(expressions: Vec<Expression>, env: Rc<RefCell<Environment>>) -> Vec<Object> {
    expressions
        .into_iter()
        .map(|exp| eval_expression(exp, env.clone()))
        .collect()
}

fn apply_function(func: Object, args: Vec<Object>) -> Object {
    match func {
        Object::Function(function) => {
            for arg in &args {
                if is_error(arg) {
                    return arg.clone();
                }
            }
            let extended_env = Rc::new(RefCell::new(Environment::new_enclosed_environment(
                function.env.clone(),
            )));
            for (param_ident, arg_obj) in function.parameters.into_iter().zip(args.into_iter()) {
                extended_env.borrow_mut().set(param_ident.value, arg_obj);
            }
            let evaluated = eval_block_statement(function.body, extended_env.clone());
            unwrap_return_value(evaluated)
        }
        Object::Builtin(builtin) => builtin(args),
        _ => Object::Error(format!("Not a function: {:?}", func)),
    }
}

fn unwrap_return_value(obj: Object) -> Object {
    if let Object::Return(value) = obj {
        *value
    } else {
        obj
    }
}

fn native_bool_to_boolean_object(input: bool) -> Object {
    if input { TRUE } else { FALSE }
}

fn is_error(obj: &Object) -> bool {
    matches!(obj, Object::Error(_))
}
