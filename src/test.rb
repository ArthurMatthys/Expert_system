require 'tempfile'
require 'open3'

PATH="../tests/"
OPTIONS=["", "-b", "-b -c"]

def     create_and_execute_tmp_file(entree, options)

    value = ""
    # Create temp file with entree values
    Tempfile.create { |f| 
        f << entree;
        f.rewind;
        value, stderr, status = Open3.capture3("./a.out #{f.path} #{options}")
        if value.empty? then
            value = stderr
        end
    }
    return value
end

def     compare_expected_result(filename)

    # Read the file in one string
    text = File.read(PATH + filename)
    
    # Parse and store with Regex
    output = Hash.new
    entree = text.scan(/\[Entree\]((.|\n)*?)\[Sortie\]/)[0][0]
    output['Mandatory'] = text.scan(/\[Sortie\]((.|\n)*?)\[Sortie_B\]/)[0][0].delete("\n ")
    output['Option B'] = text.scan(/\[Sortie_B\]((.|\n)*?)\[Sortie_C\]/)[0][0].delete("\n ")
    output['Option C'] = text.scan(/\[Sortie_C\]((.|\n)*)$/)[0][0].delete("\n ")

    a = 0
    # Loop and process verification
    output.each_with_index do | (key,value), index |
        # Retrieve execution output
        ret_value = create_and_execute_tmp_file(entree, OPTIONS[index]).delete("\n ")
        # Output color color
        colored_verdict = if (value == ret_value) then "[\e[32mok\e[0m]" else a += 1 ; "[\e[31mko\e[0m]"  end

        # Change output regarding index
        if (index == 0) then
            puts "#{key} : #{filename}".ljust(50) + "-> #{colored_verdict}".rjust(20) 
        else
            puts "#{key}".ljust(50) + "-> #{colored_verdict}".rjust(20)
        end
        # puts "ret: #{key} - value: #{ret_value}"
    end

    puts "\n"
    return a
end

def     main()

    a = 0
    # Loop on all tests
    Dir.foreach(PATH) do |filename|
        next if filename == '.' or filename == '..'
        a += compare_expected_result(filename)
    end

    if (a > 0) then
        puts "\e[31mAt least a test failed\e[0m"
    else
        puts "\e[32mAll good\e[0m"
    end
end

main()