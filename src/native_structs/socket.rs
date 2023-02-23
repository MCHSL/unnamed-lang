use std::{
    io::{Read, Write},
    net::{TcpListener, TcpStream},
};

use crate::{
    compiler::exprs::Expr,
    interpreter::{
        method_type::MethodType,
        structs::{Iterable, StructBuilder, StructInterface},
        Interpreter,
    },
};

use super::exception::Exception;

pub struct Socket {
    stream: Option<TcpStream>,
    listener: Option<TcpListener>,
}

impl Socket {
    fn new() -> Self {
        Self {
            stream: None,
            listener: None,
        }
    }

    fn from_stream(stream: TcpStream) -> Self {
        Self {
            stream: Some(stream),
            listener: None,
        }
    }

    fn listen(&mut self, host: &str, port: u16) -> Result<(), String> {
        match TcpListener::bind(format!("{host}:{port}")) {
            Ok(listener) => {
                self.listener = Some(listener);
                Ok(())
            }
            Err(e) => Err(e.to_string()),
        }
    }

    fn accept(&mut self) -> Result<Self, String> {
        match &mut self.listener {
            Some(listener) => match listener.accept() {
                Ok((stream, _)) => Ok(Self::from_stream(stream)),
                Err(e) => Err(e.to_string()),
            },
            None => Err("Not listening".to_owned()),
        }
    }

    fn connect(&mut self, host: &str, port: u16) -> Result<(), String> {
        match TcpStream::connect(format!("{host}:{port}")) {
            Ok(stream) => {
                self.stream = Some(stream);
                Ok(())
            }
            Err(e) => Err(e.to_string()),
        }
    }

    fn send(&mut self, data: &[u8]) -> Result<(), String> {
        match &mut self.stream {
            Some(stream) => match stream.write(data) {
                Ok(_) => Ok(()),
                Err(e) => Err(e.to_string()),
            },
            None => Err("Not connected".to_owned()),
        }
    }

    fn recv(&mut self, size: usize) -> Result<Vec<u8>, String> {
        match &mut self.stream {
            Some(stream) => {
                let mut buffer = vec![0; size];
                match stream.read(&mut buffer) {
                    Ok(read) => Ok(buffer[..read].to_vec()),
                    Err(e) => Err(e.to_string()),
                }
            }
            None => Err("Not connected".to_owned()),
        }
    }

    fn close(&mut self) -> Result<(), String> {
        match &mut self.stream {
            Some(stream) => match stream.shutdown(std::net::Shutdown::Both) {
                Ok(_) => {
                    self.stream = None;
                    Ok(())
                }
                Err(e) => Err(e.to_string()),
            },
            None => Err("Not connected".to_owned()),
        }
    }

    fn __str__(&mut self) -> Result<Expr, Exception> {
        Ok(Expr::Str(format!("Socket({:?})", self.stream)))
    }
}

impl StructInterface for Socket {
    fn get_method(&self, name: &str) -> Option<MethodType> {
        match name {
            "__str__" => Some(MethodType::Native(|interpreter, _args| {
                interpreter.with_this(|this: &mut Self| this.__str__())
            })),
            "connect" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let host = match args.get(0) {
                        Some(Expr::Str(host)) => host,
                        _ => return Err(Exception::new("Expected string for host")),
                    };
                    let port = match args.get(1) {
                        Some(Expr::Number(port)) => *port as u16,
                        _ => return Err(Exception::new("Expected number for port")),
                    };
                    match this.connect(host, port) {
                        Ok(_) => Ok(Expr::Null),
                        Err(e) => Err(Exception::new(e)),
                    }
                })
            })),
            "send" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let data = match args.get(0) {
                        Some(Expr::Str(data)) => data.as_bytes(),
                        _ => return Err(Exception::new("Expected string for data")),
                    };
                    match this.send(data) {
                        Ok(_) => Ok(Expr::Null),
                        Err(e) => Err(Exception::new(e)),
                    }
                })
            })),
            "recv" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let size = match args.get(0) {
                        Some(Expr::Number(size)) => *size as usize,
                        _ => return Err(Exception::new("Expected number for size")),
                    };
                    match this.recv(size) {
                        Ok(data) => Ok(Expr::Str(String::from_utf8(data).unwrap())),
                        Err(e) => Err(Exception::new(e)),
                    }
                })
            })),
            "close" => Some(MethodType::Native(|interpreter, _args| {
                interpreter.with_this(|this: &mut Self| match this.close() {
                    Ok(_) => Ok(Expr::Null),
                    Err(e) => Err(Exception::new(e)),
                })
            })),
            "listen" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let host = match args.get(0) {
                        Some(Expr::Str(host)) => host,
                        _ => return Err(Exception::new("Expected string for host")),
                    };
                    let port = match args.get(1) {
                        Some(Expr::Number(port)) => *port as u16,
                        _ => return Err(Exception::new("Expected number for port")),
                    };
                    match this.listen(host, port) {
                        Ok(_) => Ok(Expr::Null),
                        Err(e) => Err(Exception::new(e)),
                    }
                })
            })),
            "accept" => Some(MethodType::Native(|interpreter, _args| {
                let result = interpreter.with_this(|this: &mut Self| this.accept());
                match result {
                    Ok(socket) => {
                        let socket = Box::new(socket);
                        let id = interpreter.add_instance(socket);
                        Ok(Expr::Reference(id))
                    }
                    Err(e) => Err(Exception::new(e)),
                }
            })),
            "accept_many" => Some(MethodType::Native(|interpreter, _args| {
                let proxy =
                    Box::new(
                        interpreter.with_this(|this: &mut Self| SocketAcceptIteratorProxy {
                            socket: this.listener.as_ref().unwrap().try_clone().unwrap(),
                        }),
                    );

                let id = interpreter.add_instance(proxy);
                Ok(Expr::Reference(id))
            })),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct SocketBuilder {}
impl StructBuilder for SocketBuilder {
    fn construct(&self, _args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception> {
        Ok(Box::new(Socket::new()))
    }
}

pub struct SocketAcceptIteratorProxy {
    socket: TcpListener,
}

impl StructInterface for SocketAcceptIteratorProxy {
    fn iter(&self) -> Option<Box<dyn Iterable>> {
        Some(Box::new(SocketAcceptIterator {
            socket: self.socket.try_clone().unwrap(),
        }))
    }

    fn get_method(&self, _name: &str) -> Option<MethodType> {
        None
    }
}

pub struct SocketAcceptIterator {
    socket: TcpListener,
}

impl Iterable for SocketAcceptIterator {
    fn next(&mut self, interpreter: &mut Interpreter) -> Option<Expr> {
        match self.socket.accept() {
            Ok(socket) => {
                let socket = Box::new(Socket {
                    stream: Some(socket.0),
                    listener: None,
                });
                let id = interpreter.add_instance(socket);
                Some(Expr::Reference(id))
            }
            Err(e) => panic!("Fix this later: {}", e),
        }
    }
}
