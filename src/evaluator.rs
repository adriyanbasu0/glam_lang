use crate::ast::{BlockStatement, Expression, Program, Statement};
use crate::token::TokenKind;
use miette::Diagnostic;
use rand::Rng;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use thiserror::Error;

pub const NULL: Object = Object::Null;
pub const TRUE: Object = Object::Boolean(true);
pub const FALSE: Object = Object::Boolean(false);

#[derive(Error, Debug, Diagnostic)]
pub enum EvalError {
    #[error("Unknown operator: {op_kind:?}{object_type:?}")]
    #[diagnostic(
        code(evaluator::unknown_prefix_operator),
        help("This operator might not be implemented for the given type, or it's a typo.")
    )]
    UnknownPrefixOperator {
        op_kind: TokenKind,
        object_type: String,
    },
    #[error("Unknown operator: {left_type:?} {op_kind:?} {right_type:?}")]
    #[diagnostic(
        code(evaluator::unknown_infix_operator),
        help("This operator might not be implemented for the given types, or it's a typo.")
    )]
    UnknownInfixOperator {
        op_kind: TokenKind,
        left_type: String,
        right_type: String,
    },
    #[error("Type mismatch: {left_type:?} {op_kind:?} {right_type:?}")]
    #[diagnostic(
        code(evaluator::type_mismatch),
        help("Operators usually require operands of the same type.")
    )]
    TypeMismatch {
        op_kind: TokenKind,
        left_type: String,
        right_type: String,
    },
    #[error("Identifier not found: {name}")]
    #[diagnostic(
        code(evaluator::identifier_not_found),
        help("Make sure the variable is declared and spelled correctly.")
    )]
    IdentifierNotFound { name: String },
    #[error("Not a function: {object_type:?}")]
    #[diagnostic(code(evaluator::not_a_function), help("Only functions can be called."))]
    NotAFunction { object_type: String },
    #[error("Wrong number of arguments: got={got}, want={want}")]
    #[diagnostic(
        code(evaluator::wrong_number_of_arguments),
        help("Check the function signature for the correct number of arguments.")
    )]
    WrongNumberOfArguments { got: usize, want: usize },
    #[error("Argument must be an integer, got {got}")]
    #[diagnostic(
        code(evaluator::argument_must_be_integer),
        help("Ensure the arguments passed to 'rand' are integers.")
    )]
    ArgumentMustBeInteger { got: String },
    #[error("Argument to `err` must be a string, got {got}")]
    #[diagnostic(
        code(evaluator::err_argument_must_be_string),
        help("The `err` function only accepts a string as an argument.")
    )]
    ErrArgumentMustBeString { got: String },
    #[error("Failed to write to output: {source}")]
    #[diagnostic(
        code(evaluator::write_error),
        help("There was an issue writing to the output stream.")
    )]
    WriteError {
        #[from]
        source: std::io::Error,
    },
    #[error("{message}")]
    #[diagnostic(
        code(evaluator::runtime_error),
        help("A runtime error occurred during evaluation.")
    )]
    RuntimeError { message: String },
}

#[derive(Debug, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    String(String),
    Return(Box<Object>),
    Function(Function),
    Builtin(fn(Vec<Object>) -> Result<Object, EvalError>),
    Some(Box<Object>),
    Ok,
    Struct(Rc<crate::ast::StructDefinition>),
    StructInstance(HashMap<String, Object>),
    Null,
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
            Object::Struct(_) => "STRUCT",
            Object::StructInstance(_) => "STRUCT_INSTANCE",
            Object::Null => "NULL",
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
            Object::Struct(s) => {
                let fields: Vec<String> = s.fields.iter().map(|field| format!("{}: {}", field.name.value, field.field_type.value)).collect();
                write!(f, "struct {} {{ {} }}", s.name.value, fields.join(", "))
            },
            Object::StructInstance(fields) => {
                let field_strings: Vec<String> = fields.iter().map(|(name, value)| format!("{}: {}", name, value)).collect();
                write!(f, "{{ {} }}", field_strings.join(", "))
            },
            Object::Null => write!(f, "null"),
        }
    }
}

pub struct Environment {
    store: HashMap<String, Object>,
    outer: Option<Rc<RefCell<Environment>>>,
    pub writer: Rc<RefCell<dyn std::io::Write>>,
}

pub fn builtin_type(args: Vec<Object>) -> Result<Object, EvalError> {
    if args.len() != 1 {
        return Err(EvalError::WrongNumberOfArguments {
            got: args.len(),
            want: 1,
        });
    }
    Ok(Object::String(args[0].type_str().to_string()))
}

pub fn builtin_rand(args: Vec<Object>) -> Result<Object, EvalError> {
    if args.len() != 2 {
        return Err(EvalError::WrongNumberOfArguments {
            got: args.len(),
            want: 2,
        });
    }

    let min = match args[0] {
        Object::Integer(i) => i,
        _ => {
            return Err(EvalError::ArgumentMustBeInteger {
                got: args[0].type_str().to_string(),
            });
        }
    };

    let max = match args[1] {
        Object::Integer(i) => i,
        _ => {
            return Err(EvalError::ArgumentMustBeInteger {
                got: args[1].type_str().to_string(),
            });
        }
    };

    let mut rng = rand::thread_rng();
    Ok(Object::Integer(rng.gen_range(min..=max)))
}

pub fn builtin_some(args: Vec<Object>) -> Result<Object, EvalError> {
    if args.len() != 1 {
        return Err(EvalError::WrongNumberOfArguments {
            got: args.len(),
            want: 1,
        });
    }
    Ok(Object::Some(Box::new(args[0].clone())))
}

pub fn builtin_err(args: Vec<Object>) -> Result<Object, EvalError> {
    if args.len() != 1 {
        return Err(EvalError::WrongNumberOfArguments {
            got: args.len(),
            want: 1,
        });
    }
    match &args[0] {
        Object::String(s) => Err(EvalError::RuntimeError { message: s.clone() }),
        _ => Err(EvalError::ErrArgumentMustBeString {
            got: args[0].type_str().to_string(),
        }),
    }
}

pub fn builtin_ok(args: Vec<Object>) -> Result<Object, EvalError> {
    if !args.is_empty() {
        return Err(EvalError::WrongNumberOfArguments {
            got: args.len(),
            want: 0,
        });
    }
    Ok(Object::Ok)
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

pub fn eval(program: Program, env: &mut Rc<RefCell<Environment>>) -> Result<Object, EvalError> {
    let mut result = NULL;
    for statement in program.statements {
        result = eval_statement(statement, env.clone())?;
        if let Object::Return(value) = result {
            return Ok(*value);
        }
    }
    Ok(result)
}

fn eval_statement(
    statement: Statement,
    env: Rc<RefCell<Environment>>,
) -> Result<Object, EvalError> {
    match statement {
        Statement::Expression(expr) => eval_expression(expr.expression, env),
        Statement::Return(ret_stmt) => {
            let val = eval_expression(ret_stmt.return_value, env)?;
            Ok(Object::Return(Box::new(val)))
        }
        Statement::Let(let_stmt) => {
            let val = eval_expression(let_stmt.value, env.clone())?;
            Ok(env.borrow_mut().set(let_stmt.name.value, val))
        }
        Statement::Print(print_stmt) => eval_print_statement(print_stmt.expression, env),
        Statement::Struct(struct_def) => {
            let name = struct_def.name.value.clone();
            let struct_obj = Object::Struct(Rc::new(struct_def));
            env.borrow_mut().set(name, struct_obj);
            Ok(NULL)
        }
    }
}

fn eval_print_statement(
    expression: Expression,
    env: Rc<RefCell<Environment>>,
) -> Result<Object, EvalError> {
    let value = eval_expression(expression, env.clone())?;
    let env_ref = env.borrow_mut();
    let mut writer = env_ref.writer.borrow_mut();
    writeln!(writer, "{}", value)?;
    writer.flush()?;
    Ok(NULL)
}

fn eval_expression(
    expression: Expression,
    env: Rc<RefCell<Environment>>,
) -> Result<Object, EvalError> {
    match expression {
        Expression::IntLiteral(int) => Ok(Object::Integer(int.value)),
        Expression::Boolean(boolean) => Ok(native_bool_to_boolean_object(boolean.value)),
        Expression::StringLiteral(s) => Ok(Object::String(s.value)),
        Expression::Null => Ok(NULL),
        Expression::Prefix(prefix) => {
            let right = eval_expression(*prefix.right, env)?;
            eval_prefix_expression(prefix.operator, right)
        }
        Expression::Infix(infix) => {
            let left = eval_expression(*infix.left, env.clone())?;
            let right = eval_expression(*infix.right, env)?;
            eval_infix_expression(infix.operator, left, right)
        }
        Expression::If(if_exp) => {
            let condition = eval_expression(*if_exp.condition, env.clone())?;
            Ok(if condition.is_truthy() {
                eval_block_statement(if_exp.consequence, env)?
            } else if let Some(alt) = if_exp.alternative {
                eval_block_statement(alt, env)?
            } else {
                NULL
            })
        }
        Expression::Identifier(ident) => eval_identifier(ident, env),
        Expression::Function(func) => Ok(Object::Function(Function {
            parameters: func.parameters,
            body: func.body,
            env: env, // Capture the current Rc<RefCell<Environment>> directly
        })),
        Expression::Call(call_exp) => {
            let function = eval_expression(*call_exp.function, env.clone())?;
            let args = eval_expressions(call_exp.arguments, env)?;
            apply_function(function, args)
        },
        Expression::Access(access_exp) => {
            let object = eval_expression(*access_exp.object, env.clone())?;
            match object {
                Object::StructInstance(fields) => {
                    if let Some(field_value) = fields.get(&access_exp.field.value) {
                        Ok(field_value.clone())
                    } else {
                        Err(EvalError::RuntimeError {
                            message: format!("Field '{}' not found in struct instance", access_exp.field.value),
                        })
                    }
                },
                _ => Err(EvalError::RuntimeError {
                    message: format!("Cannot access fields on non-struct object of type {}", object.type_str()),
                }),
            }
        },
        Expression::StructInstance(struct_instance_exp) => {
            let struct_def_name = struct_instance_exp.struct_name.value;
            let struct_obj = env.borrow().get(&struct_def_name);

            if let Some(Object::Struct(struct_def_rc)) = struct_obj { // struct_def_rc is Rc<ast::StructDefinition>
                let mut instance_fields: HashMap<String, Object> = HashMap::new();

                for (field_name_ident, field_value_expr) in struct_instance_exp.fields {
                    // Check if field_name_ident exists in struct_def_rc.fields
                    let field_exists_in_def = struct_def_rc.fields.iter()
                        .any(|f_def| f_def.name.value == field_name_ident.value);

                    if !field_exists_in_def {
                        return Err(EvalError::RuntimeError {
                            message: format!("Field '{}' not found in struct '{}'",
                                field_name_ident.value, struct_def_name),
                        });
                    }

                    let field_value = eval_expression(field_value_expr, env.clone())?;
                    instance_fields.insert(field_name_ident.value, field_value);
                }
                Ok(Object::StructInstance(instance_fields))
            } else {
                Err(EvalError::RuntimeError {
                    message: format!("Struct '{}' not defined", struct_def_name),
                })
            }
        }
    }
}

fn eval_block_statement(
    block: BlockStatement,
    env: Rc<RefCell<Environment>>,
) -> Result<Object, EvalError> {
    let mut result = NULL;
    for statement in block.statements {
        result = eval_statement(statement, env.clone())?;
        if let Object::Return(_) = result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_prefix_expression(
    operator: crate::token::Token,
    right: Object,
) -> Result<Object, EvalError> {
    match operator.kind {
        TokenKind::Bang => Ok(eval_bang_operator_expression(right)),
        TokenKind::Minus => eval_minus_operator_expression(right),
        _ => Err(EvalError::UnknownPrefixOperator {
            op_kind: operator.kind,
            object_type: right.type_str().to_string(),
        }),
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

fn eval_minus_operator_expression(right: Object) -> Result<Object, EvalError> {
    if let Object::Integer(value) = right {
        Ok(Object::Integer(-value))
    } else {
        Err(EvalError::UnknownPrefixOperator {
            op_kind: TokenKind::Minus,
            object_type: right.type_str().to_string(),
        })
    }
}

fn eval_infix_expression(
    operator: crate::token::Token,
    left: Object,
    right: Object,
) -> Result<Object, EvalError> {
    match (left, right) {
        (Object::Integer(l_val), Object::Integer(r_val)) => {
            eval_integer_infix_expression(operator, l_val, r_val)
        }
        (Object::Boolean(l_val), Object::Boolean(r_val)) => {
            eval_boolean_infix_expression(operator, l_val, r_val)
        }
        (Object::String(l_val), Object::String(r_val)) => {
            if operator.kind == TokenKind::Plus {
                Ok(Object::String(format!("{}{}", l_val, r_val)))
            } else {
                Err(EvalError::UnknownInfixOperator {
                    op_kind: operator.kind,
                    left_type: l_val,
                    right_type: r_val,
                })
            }
        }
        (l, r) if l.type_str() != r.type_str() => Err(EvalError::TypeMismatch {
            op_kind: operator.kind,
            left_type: l.type_str().to_string(),
            right_type: r.type_str().to_string(),
        }),
        (l, r) => Err(EvalError::UnknownInfixOperator {
            op_kind: operator.kind,
            left_type: l.type_str().to_string(),
            right_type: r.type_str().to_string(),
        }),
    }
}

fn eval_integer_infix_expression(
    operator: crate::token::Token,
    left: i64,
    right: i64,
) -> Result<Object, EvalError> {
    match operator.kind {
        TokenKind::Plus => Ok(Object::Integer(left + right)),
        TokenKind::Minus => Ok(Object::Integer(left - right)),
        TokenKind::Asterisk => Ok(Object::Integer(left * right)),
        TokenKind::Slash => Ok(Object::Integer(left / right)),
        TokenKind::Lt => Ok(native_bool_to_boolean_object(left < right)),
        TokenKind::Gt => Ok(native_bool_to_boolean_object(left > right)),
        TokenKind::Eq => Ok(native_bool_to_boolean_object(left == right)),
        TokenKind::NotEq => Ok(native_bool_to_boolean_object(left != right)),
        _ => Err(EvalError::UnknownInfixOperator {
            op_kind: operator.kind,
            left_type: Object::Integer(left).type_str().to_string(),
            right_type: Object::Integer(right).type_str().to_string(),
        }),
    }
}

fn eval_boolean_infix_expression(
    operator: crate::token::Token,
    left: bool,
    right: bool,
) -> Result<Object, EvalError> {
    match operator.kind {
        TokenKind::Eq => Ok(native_bool_to_boolean_object(left == right)),
        TokenKind::NotEq => Ok(native_bool_to_boolean_object(left != right)),
        _ => Err(EvalError::UnknownInfixOperator {
            op_kind: operator.kind,
            left_type: native_bool_to_boolean_object(left).type_str().to_string(),
            right_type: native_bool_to_boolean_object(right).type_str().to_string(),
        }),
    }
}

fn eval_identifier(
    ident: crate::ast::Identifier,
    env: Rc<RefCell<Environment>>,
) -> Result<Object, EvalError> {
    if let Some(val) = env.borrow().get(&ident.value) {
        return Ok(val);
    }
    Err(EvalError::IdentifierNotFound { name: ident.value })
}

fn eval_expressions(
    expressions: Vec<Expression>,
    env: Rc<RefCell<Environment>>,
) -> Result<Vec<Object>, EvalError> {
    expressions
        .into_iter()
        .map(|exp| eval_expression(exp, env.clone()))
        .collect() // This will implicitly use FromIterator for Result<Vec<Object>>
}

fn apply_function(func: Object, args: Vec<Object>) -> Result<Object, EvalError> {
    match func {
        Object::Function(function) => {
            let extended_env = Rc::new(RefCell::new(Environment::new_enclosed_environment(
                function.env.clone(),
            )));
            for (param_ident, arg_obj) in function.parameters.into_iter().zip(args.into_iter()) {
                extended_env.borrow_mut().set(param_ident.value, arg_obj);
            }
            let evaluated = eval_block_statement(function.body, extended_env.clone())?;
            Ok(unwrap_return_value(evaluated))
        }
        Object::Builtin(builtin) => builtin(args),
        _ => Err(EvalError::NotAFunction {
            object_type: func.type_str().to_string(),
        }),
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
