import type {Meta, StoryObj} from '@storybook/react';

import HomePage from "../components/HomePage";

const meta = {
  title: 'Example/Home',
  component: HomePage,
  tags: ['autodocs'],
} satisfies Meta<typeof HomePage>;

export default meta;
type Story = StoryObj<typeof HomePage>;

export const Primary: Story = {};
