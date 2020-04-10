require 'tempfile'

PATH="../tests/"

def     create_and_execute_tmp_file(entree, options)

    value = ""
    # Create temp file with entree values
    Tempfile.create { |f| 
        f << entree;
        f.rewind;
        value = `./a.out #{f.path} #{options}`
    }
    return value
end

def     compare_expected_result(filename)

    # Read the file in one string
    text = File.read(PATH + filename)
    
    # Parse with Regex
    entree = text.scan(/\[Entree\]((.|\n)*?)\[Sortie\]/)[0][0]
    sortie = text.scan(/\[Sortie\]((.|\n)*?)\[options\]/)[0][0].delete("\n")
    options = text.scan(/\[options\]((.|\n)*)$/)[0][0].delete("\n").to_s

    # Retrieve execution output
    ret_value = create_and_execute_tmp_file(entree, options).delete("\n")

    # Output
    if (sortie == ret_value) then
        puts "#{filename} -> [\e[32mok\e[0m]"
    else
        puts "#{filename} -> [\e[31mko\e[0m]"
    end

end


def     main()
    
    # Loop on all tests
    Dir.foreach(PATH) do |filename|
        next if filename == '.' or filename == '..'
        compare_expected_result(filename)
    end
end

main()