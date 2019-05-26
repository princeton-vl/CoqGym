# Preprocessor.
require 'erb'

# The version of Coq.
version = `coqc -v`.match(/version ([^(]*) \(/)[1]

Dir.glob("src/*.v.erb") do |file_name|
  renderer = ERB.new(File.read(file_name, encoding: "UTF-8"))
  output_name = file_name[0..-5]
  File.open(output_name, "w") do |file|
    file << renderer.result()
  end
  puts "#{file_name} -> #{output_name}"
end
