use std::path::PathBuf;
use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Write};
use serde_json::{Value, from_str, json};
use std::collections::HashMap;

mod compilation_user;
mod execution_user;
mod input_user;
mod parser_user;
mod type_analysis_user;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

fn main() {
    let result = start();
    match result {
        Ok(vec) => {
            // for ast in &vec {
            //     println!("{}", ast);
            // }
        },
        Err(_) => println!("Error occurred"),
    }
}

fn start() -> Result<Value, ()> {
    use input_user::Input;

    // 获取命令行参数
    let args: Vec<String> = std::env::args().collect();

    let input_path = match args.get(1) {
        Some(s) => s.to_string(),
        None => String::from("../MultiFile/func.circom")
    };
    let output_path = match args.get(2) {
        Some(s) => s.to_string(),
        None => String::from("../MultiFile/ast.json")
    };

    let input = PathBuf::from(input_path);
    let link_libraries:Vec<PathBuf> = Vec::new();
    // let user_input = Input::new()?;

    let user_input = Input {
        input_program: input,
        link_libraries
    };

    let json_vec = parser_user::parse_project(&user_input)?;

    // let mut ast_json = OpenOptions::new()
    //     .write(true)
    //     .truncate(true)
    //     .create_new(true)
    //     .open(&output_path)
    //     .unwrap_or_else(|_| File::create(&output_path).unwrap());
    // let mut writer = BufWriter::new(ast_json);

    // 将 Vec<String> 转换为 Vec<serde_json::Value>
    let mut json_values: Vec<Value> = json_vec
        .into_iter()
        .map(|json_str| from_str(&json_str).expect("Invalid JSON"))
        .collect();

    // 获取第一个 JSON 作为目标
    let mut target_json = json_values.remove(0); // 第一个json值

    // 确保第一个 JSON 中的 `data` 是一个数组
    let target_array = target_json["definitions"].as_array_mut().expect("data should be an array");

    // 遍历剩下的 JSON 对象，将它们的 `data` 属性的元素合并到目标数组中
    for json_value in json_values {
        if let Some(data_array) = json_value["definitions"].as_array() {
            // 将当前 JSON 的 "data" 数组中的元素加入到目标 JSON 的 "data" 数组中
            for item in data_array {
                target_array.push(item.clone());
            }
        }
    }

    // 打印最终合并后的 JSON
    // println!("{}", target_json);


    // for ast in &json_vec {
    //     writer.write_all(ast.as_bytes()).unwrap();
    //     writer.write_all(b"\n").unwrap();
    // }

    // 指定文件路径
    let file_path = output_path; // 可以替换成你想要的路径

    // 打开文件，准备写入
    let mut file = File::create(file_path).expect("Unable to create file");

    // 将合并后的 JSON 写入文件
    serde_json::to_writer_pretty(&mut file, &target_json).expect("Unable to write data");

    Ok(target_json)
}
