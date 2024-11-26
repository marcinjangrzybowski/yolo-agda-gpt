from openai import OpenAI

# Store your OpenAI API key here
API_KEY = ??


client = OpenAI(api_key=API_KEY)
import sys


def main():
    if len(sys.argv) != 4:
        print("Usage: python chatgpt_api_wrapper.py <template_file> <placeholder1> <placeholder2>")
        sys.exit(1)

    # Get command-line arguments
    template_file = sys.argv[1]
    placeholder1 = sys.argv[2]
    placeholder2 = sys.argv[3]

    # Set the API key

    # Read the template from the file
    try:
        with open(template_file, 'r') as file:
            template = file.read()
    except FileNotFoundError:
        print(f"Error: File '{template_file}' not found.")
        sys.exit(1)

    # Replace placeholders in the template
    prompt = template.replace("{placeholder1}", placeholder1).replace("{placeholder2}", placeholder2)

    # Call the OpenAI API
    try:
        response = client.chat.completions.create(model="gpt-4",
        messages=[{"role": "user", "content": prompt}])
        # Print the response content
        print(response.choices[0].message.content)
    except Exception as e:
        print(f"Error calling OpenAI API: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
