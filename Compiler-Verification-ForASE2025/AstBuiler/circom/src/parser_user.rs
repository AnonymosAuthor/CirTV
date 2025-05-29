use super::input_user::Input;
use program_structure::program_archive::ProgramArchive;
use crate::VERSION;


pub fn parse_project(input_info: &Input) -> Result<Vec<String>, ()> {
    let initial_file = input_info.input_file().to_string();
    let mut json_vec:Vec<String> = Vec::new();
    let library_vec = input_info.get_link_libraries().to_vec();
    let result_program_archive = parser::run_parser(initial_file, VERSION, library_vec, &mut json_vec);
    match result_program_archive {
        Result::Err((file_library, report_collection)) => {
            Result::Err(())
        }
        Result::Ok((temp, warnings)) => {
            Result::Ok(json_vec)
        }
    }
}
