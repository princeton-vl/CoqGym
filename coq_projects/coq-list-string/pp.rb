# Preprocessor.
require 'erb'

# The version of Coq.
version = `coqc -v`.match(/version ([^(]*) \(/)[1]

Dir.glob("src/*.v.erb") do |file_name|
  renderer = ERB.new(File.read(file_name, encoding: "UTF-8"))
  File.open(file_name[0..-5], "w") do |file|
    file << renderer.result()
  end
  puts file_name
end
